-- Prove2me | Definitions.Def_TSPHeuristics_Shared_Insertion
-- name    : TSPHeuristics_Shared_Insertion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:55:51.556984+00:00
-- url     : https://prove2.me/theorems/f47a2835-f1b1-42a1-b647-fc1b7da14cad
-- title:
--   TOUR(T, k), COST(T, k), insertion methods, nearest insertion and cheapest insertion
-- statement:
--   Let $(N, d)$ be a traveling salesman graph with $n$ nodes and $T$ a subtour.
--
--   1. **Inserting a node.** For a node $k \notin T$, $\mathrm{TOUR}(T,k)$ is obtained as follows. If $T$ passes through more than one node, choose an edge $(x,y)$ of $T$ minimizing $d(x,k) + d(k,y) - d(x,y)$ (3.1), delete $(x,y)$ and add $(x,k)$ and $(k,y)$. If $T$ is a single node $i$, $\mathrm{TOUR}(T,k)$ is the two-node tour with edges $(i,k)$ and $(k,i)$. Ties between edges are broken arbitrarily.
--   2. **Cost.** $\mathrm{COST}(T,k) = \mathrm{len}(\mathrm{TOUR}(T,k)) - \mathrm{len}(T)$; for $|T| \ge 2$ it is the minimum of (3.1) over the edges of $T$.
--   3. **Insertion method.** A run constructs subtours $T_1, \dots, T_n$ and nodes $a_0, \dots, a_{n-1}$ with $T_1 = \{a_0\}$ and, for $1 \le i < n$, $a_i \notin T_i$ and $T_{i+1} = \mathrm{TOUR}(T_i, a_i)$ (3.2). $T_n$ is the approximation, and INSERT is its length.
--   4. **Nearest insertion.** With $d(T,p) = \min\{d(x,p) : x \in T\}$ (4.1), the run is a nearest-insertion run if for every $1 \le i < n$
--   $$
--   d(T_i, a_i) = \min\{d(T_i, x) : x \in N - T_i\} \qquad (4.2).
--   $$
--   5. **Cheapest insertion.** The run is a cheapest-insertion run if for every $1 \le i < n$
--   $$
--   \mathrm{COST}(T_i, a_i) = \min\{\mathrm{COST}(T_i, x) : x \in N - T_i\} \qquad (4.3).
--   $$
--
--   The start node $a_0$ is arbitrary, and so is the choice among tied candidates in (4.2) and (4.3).
--
--   These are the two insertion heuristics that the paper bounds by $2(1 - 1/n)$ times the optimal tour (Theorem 4 and its Corollary, pp. 573–574) and shows that bound to be tight (Theorem 5, pp. 575–576). The definition is shared by two missions of this paper: 03-nearest-cheapest (the upper bound, §4, pp. 572–574) and 04-k-optimal-tight (the tightness instance of Theorem 5, pp. 575–576, and the Corollary to Theorem 6, p. 581); the definitions themselves are on pp. 570–572.
--
--   **Formalization Note** A subtour is a list of distinct nodes. Inserting $k$ at list position $pos \in \{0, \dots, |T|\}$ replaces the edge between the entries at $pos-1$ and $pos$ (positions $0$ and $|T|$ both replace the closing edge), so "$T'$ is $\mathrm{TOUR}(T,k)$" is encoded as: $T'$ is $T$ with $k$ inserted at some position whose resulting length is minimal over all positions. COST is the minimum over positions of the new length minus the old; it is only applied to $k \notin T$. The subtour index is 1-based as printed: `T 1 = [a 0]` and `T n` is the final tour. The distance $d(T,p)$ is computed in $\mathbb{R} \cup \{+\infty\}$ (it is $+\infty$ only for the empty list, which is never a subtour of a run), so no junk value enters (4.2). The rules (4.2) and (4.3) are stated as "$a_i$ is at least as good as every $x \notin T_i$", which is equivalent to the printed equalities with a minimum.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 570, §3 (TOUR(T, k), eq. (3.1)); p. 571 (insertion method, eq. (3.2), COST(T, k), INSERT); p. 572, §4, eqs. (4.1), (4.2), (4.3)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel

namespace TSPHeuristics.Shared

/-- `T'` is TOUR(T, k) (p. 570): `k` is not on the subtour `T`, and `T'` is obtained by inserting
`k` into `T` at a position that minimizes the length of the resulting subtour. Inserting at
position `pos` with `0 < pos < T.length` replaces the edge between the entries `pos - 1` and `pos`,
and `pos = 0` or `pos = T.length` replaces the closing edge, so the minimization over positions is
the minimization of (3.1) over the edges `(x, y)` of `T`. For a one-node `T = [i]` every position
gives the two-node tour on `i` and `k`. Ties between positions are resolved arbitrarily. -/
def IsInsertion {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n)
    (T' : List (Fin n)) : Prop :=
  k ∉ T ∧ ∃ pos ≤ T.length, T' = T.insertIdx pos k ∧
    ∀ pos' ≤ T.length, cycleLength d T' ≤ cycleLength d (T.insertIdx pos' k)

/-- COST(T, k) (p. 571): the length of TOUR(T, k) minus the length of `T`, i.e. the least
increase in length over all insertion positions. Used only for `k ∉ T`. -/
def insCost {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n) : ℝ :=
  (Finset.range (T.length + 1)).inf' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
      (fun pos => cycleLength d (T.insertIdx pos k)) - cycleLength d T

/-- An insertion method run (p. 571) on a graph with `n` nodes, with the paper's 1-based subtour
index: `T 1` is the one-node subtour `[a 0]`, and for `1 ≤ i < n` the node `a i` is not in `T i`
and `T (i + 1)` is TOUR(`T i`, `a i`). `T n` is the approximation; the values of `T` and `a`
outside these indices are irrelevant. -/
def IsInsertionRun {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) :
    Prop :=
  T 1 = [a 0] ∧ ∀ i, 1 ≤ i → i < n → IsInsertion d (T i) (a i) (T (i + 1))

/-- The distance d(T, p) between a subtour and a node, (4.1): `min {d(x, p) : x ∈ T}`, computed in
`WithTop ℝ` so that no junk value arises (it is `⊤` only for the empty list, which is never a
subtour). -/
def distToTour {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (p : Fin n) : WithTop ℝ :=
  T.toFinset.inf (fun x => ((d x p : ℝ) : WithTop ℝ))

/-- Nearest insertion, (4.2): for `1 ≤ i < n`, `d(T_i, a_i) ≤ d(T_i, x)` for every `x ∉ T_i`. -/
def IsNearestRule {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) :
    Prop :=
  ∀ i, 1 ≤ i → i < n → ∀ x, x ∉ T i → distToTour d (T i) (a i) ≤ distToTour d (T i) x

/-- Cheapest insertion, (4.3): for `1 ≤ i < n`, `COST(T_i, a_i) ≤ COST(T_i, x)` for every
`x ∉ T_i`. -/
def IsCheapestRule {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) :
    Prop :=
  ∀ i, 1 ≤ i → i < n → ∀ x, x ∉ T i → insCost d (T i) (a i) ≤ insCost d (T i) x

end TSPHeuristics.Shared


