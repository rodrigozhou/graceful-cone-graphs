#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <chrono>
#include <algorithm>
using namespace std;

// UTILS {

void print_labeling(const int *lbl, int n) {
    for (int i = 0; i < n; i++)
        printf("%d -> %d\n", i, lbl[i]);
    puts("");
}

// } UTILS

#define MAX 256

/**
 * It is assumed that the vertices of the cycle are {0, ..., cycle-1} and
 * the vertices of the stable set are {cycle, ..., n-1}.
 * The vertices from stable set must be labeled from `n-1' to `cycle'.
 */

int cycle, stable;  // sizes of the cycle and stable set
int n, m;           // total number of vertices and edges
int lbl[MAX];       // lbl[u]  = label of vertex u or -1
int ilbl[MAX];      // ilbl[x] = vertex with label x or -1
bool elbl[MAX];     // elbl[x] = true if there is an edge with label x
int next_stable;    // next vertex from stable set to be labeled

void clear() {
    memset(lbl, -1, n * sizeof(int));
    memset(ilbl, -1, (m+1) * sizeof(int));
    memset(elbl, 0, (m+1) * sizeof(bool));
    next_stable = n-1;
}

/**
 * Auxiliary functions for bt().
 */
int aux[MAX], qaux;
bool check(int u, int val) {
    // check if it is possible to label vertex `u' with `val'
    // `aux' is filled with new generated edge labels
    qaux = 0;
    if (u < cycle) {
        int v = u == 0 ? cycle-1 : u-1;
        if (lbl[v] != -1) {
            if (elbl[abs(val - lbl[v])])
                return 0;
            aux[qaux++] = abs(val - lbl[v]);
        }
        v = u+1 < cycle ? u+1 : 0;
        if (lbl[v] != -1) {
            if (elbl[abs(val - lbl[v])])
                return 0;
            aux[qaux++] = abs(val - lbl[v]);
        }
        for (int v = next_stable+1; v < n; v++) {
            if (elbl[abs(val - lbl[v])])
                return 0;
            aux[qaux++] = abs(val - lbl[v]);
        }
    }
    else {
        for (int v = 0; v < cycle; v++) {
            if (lbl[v] != -1) {
                if (elbl[abs(val - lbl[v])])
                    return 0;
                aux[qaux++] = abs(val - lbl[v]);
            }
        }
    }
    sort(aux, aux + qaux);
    return unique(aux, aux + qaux) == aux + qaux;
}

/**
 * Label the vertex `u' with `val'.
 * Vertices from stable set must be labeled from `n-1' to `cycle'.
 */
void color(int u, int val, bool with_check = false) {
    // `check' function must be called before or
    // `color' function must be called with `with_check = true'
    if (with_check && !check(u, val))
        printf("color -> check: fail, u = %d, val = %d\n", u, val);
    lbl[u] = val;
    ilbl[val] = u;
    for (int i = 0; i < qaux; i++)
        elbl[aux[i]] = true;
    if (u >= cycle)
        next_stable--;
}

/**
 * Unlabel the vertex `u' with `val'.
 * Vertices from stable set must be unlabeled from the most recent
 * labeled one to the oldest one.
 */
void uncolor(int u) {
    if (u < cycle) {
        int v = u == 0 ? cycle-1 : u-1;
        if (lbl[v] != -1)
            elbl[abs(lbl[u] - lbl[v])] = false;
        v = u+1 < cycle ? u+1 : 0;
        if (lbl[v] != -1)
            elbl[abs(lbl[u] - lbl[v])] = false;
        for (int v = next_stable+1; v < n; v++)
            elbl[abs(lbl[u] - lbl[v])] = false;
    }
    else {
        for (int v = 0; v < cycle; v++)
            if (lbl[v] != -1)
                elbl[abs(lbl[u] - lbl[v])] = false;
        next_stable++;
    }
    ilbl[lbl[u]] = -1;
    lbl[u] = -1;
}

int qnt_sols = 0;
bool single_solution = false;   // false => find all solutions
bool full_search = true;        // false => ignore case `both = true'

int bt(int next_lbl) {
    // search for next edge label not used yet
    while (elbl[next_lbl])
        next_lbl--;

    if (next_lbl == 0) {
        // every edge label appeared once => graceful labeling found
        print_labeling(lbl, n);
        qnt_sols += 1;
        return single_solution;
    }

    for (int k = next_lbl; k <= m; k++) {
        int kc = k - next_lbl;  // |k - kc| = next_lbl
        int u = -1;             // vertex with label k or kc, or -1
        int free = -1;          // label not used
        bool both = false;      // indicate if both labels were not used
        if (ilbl[k] == -1 && ilbl[kc] != -1)
            u = ilbl[kc], free = k;
        else if (ilbl[k] != -1 && ilbl[kc] == -1)
            u = ilbl[k], free = kc;
        else if (ilbl[k] == -1 && ilbl[kc] == -1)
            both = true;
        else
            continue;
        if (both) {
            if (!full_search) continue;
            for (int u = 0; u < cycle; u++) {
                if (lbl[u] != -1) continue;
                for (int opt = 0; opt < 2; opt++, swap(k, kc)) {
                    if (!check(u, k)) continue;
                    color(u, k);
                    int v = u+1 < cycle ? u+1 : 0;
                    if (lbl[v] == -1 && check(v, kc)) {
                        color(v, kc);
                        if (bt(next_lbl-1)) return 1;
                        uncolor(v);
                    }
                    v = next_stable;
                    if (v >= cycle && check(v, kc)) {
                        color(v, kc);
                        if (bt(next_lbl-1)) return 1;
                        uncolor(v);
                    }
                    uncolor(u);
                }
            }
        }
        else {
            if (u < cycle) {
                int v = u == 0 ? cycle-1 : u-1;
                if (lbl[v] == -1 && check(v, free)) {
                    color(v, free);
                    if (bt(next_lbl-1)) return 1;
                    uncolor(v);
                }
                v = u+1 < cycle ? u+1 : 0;
                if (lbl[v] == -1 && check(v, free)) {
                    color(v, free);
                    if (bt(next_lbl-1)) return 1;
                    uncolor(v);
                }
                v = next_stable;
                if (v >= cycle && check(v, free)) {
                    color(v, free);
                    if (bt(next_lbl-1)) return 1;
                    uncolor(v);
                }
            }
            else {
                for (int v = 0; v < cycle; v++) {
                    if (lbl[v] != -1) continue;
                    if (check(v, free)) {
                        color(v, free);
                        if (bt(next_lbl-1)) return 1;
                        uncolor(v);
                    }
                }
            }
        }
    }
    return 0;
}

/**
 * Backtracking on vertices
 * Label the stable set first: choose `stable' labels from [0, m].
 * Then, label the vertices of the cycle by trying every label not used yet.
 * Just call `bt_dumb(n-1)'.
 */
int bt_dumb(int u) {
    while (u >= 0 && lbl[u] != -1) u--;
    if (u < 0) {
        print_labeling(lbl, n);
        return single_solution;
    }
    if (u >= cycle) {
        int free = u == n-1 ? m : lbl[u+1] - 1;
        for (; free >= u - cycle; free--) {
            color(u, free, true);
            if (bt_dumb(u-1)) return 1;
            uncolor(u);
        }
    }
    else {
        for (int free = 0; free <= m; free++) {
            if (ilbl[free] != -1) continue;
            if (!check(u, free)) continue;
            color(u, free);
            if (bt_dumb(u-1)) return 1;
            uncolor(u);
        }
    }
    return 0;
}

/**
 * It is assumed cycle >= 3 and stable >= 2.
 */
int is_graceful_cone() {
    clear();

    // wlog, vertex label 0 is in the cycle
    color(0, 0, true);

    // case 1: edge label m is in the cycle
    puts("start 0-m cycle");
    color(1, m, true);

    // case 1.1: edge label m-1 is in the cycle
    //           wlog, vertex label 1 is in the cycle adjacent to vertex label m
    puts("start 0-m-1 cycle");
    color(2, 1, true);
    if (bt(m)) return 1;
    uncolor(2);
    puts("end 0-m-1 cycle");

    // case 1.2: edge label m-1 is in a crossing edge
    //           wlog, vertex label 1 is in the stable set
    puts("start 0-m cycle 1 stable");
    color(n-1, 1, true);
    if (bt(m)) return 1;
    uncolor(n-1);
    puts("end 0-m cycle 1 stable");

    uncolor(1);
    puts("end 0-m cycle");

    // case 2
    for (int k = 1; k <= stable; k++) {
        // loop invariant: the only vertex label in the cycle is 0,
        // the vertex labels in [m-k+2, m] are in the stable set,
        // the edge label m-k+1 must be in a crossing edge, and
        // we want to create edge label m-k.
        printf("setting next_stable with color m-%d\n", k);
        color(next_stable, m-k+1, true);

        // case a: edge label m-k is in the cycle adjacent to vertex label 0
        printf("start 0-(m-%d) cycle\n", k);
        color(1, m-k, true);
        if (bt(m)) return 1;
        uncolor(1);
        printf("end 0-(m-%d) cycle\n", k);

        // case b: edge label m-k is in a crossing edge, m-k = (m-j)-(k-j), j=0..k-1
        //         wlog, vertex label k is in one of the vertex of the cycle
        //         for j=1..k-1, (k-j) must be in the cycle, and it was considered
        //         in the previous iteration
        for (int i = 1; i <= cycle/2; i++) {
            printf("start %d cycle on %d-th\n", k, i);
            color(i, k, true);
            if (bt(m)) return 1;
            uncolor(i);
            printf("end %d cycle on %d-th\n", k, i);
        }
    }

    return 0;
}

/**
 * Custom function to find specific labelings.
 * Must comply with the restrictions of the previous functions.
 * After fixing the vertex labels for some vertices, call `bt(m)'.
 *
 * C_p + I_q, p = 1 (mod 4), p > 1
 */
int is_graceful_cone_cycle_1_mod_4() {
    clear();

    int opt = 0;

    if (opt == 0) {
        color(0, 0, true);
        color(1, m, true);
        color(cycle-1, m-1, true);

        // since it is labeling all the stable set first,
        // it won't break the algorithm.
        color(cycle, 2, true);
        for (int i = 1; i < stable; i++) {
            int val = i * cycle + 3;
            color(cycle+i, val, true);
        }

        bt(m);
    }
    else if (opt == 1) {
        color(0, 0, true);
        color(1, m, true);

        // since it is labeling all the stable set first,
        // it won't break the algorithm.
        color(cycle, 1, true);
        for (int i = 1; i < stable; i++) {
            int val = i * cycle + 4;
            color(cycle+i, val, true);
        }

        bt(m);
    }

    return 0;
}

int main() {
    scanf("%d %d", &cycle, &stable);

    n = cycle + stable;
    m = cycle * (stable + 1);

    auto start_time = chrono::high_resolution_clock::now();

    printf("cycle = %d, stable = %d\n", cycle, stable);

    single_solution = false;
    full_search = true;
    is_graceful_cone();
    // is_graceful_cone_cycle_1_mod_4();

    printf("qnt_sols = %d\n", qnt_sols);
    printf("cycle = %d, stable = %d\n", cycle, stable);

    auto end_time = chrono::high_resolution_clock::now();
    auto time_span = chrono::duration_cast<chrono::nanoseconds>(end_time - start_time);
    double microseconds = time_span.count() / 1000.0;

    printf("total time: %lf ms\n", microseconds / 1000);
}
