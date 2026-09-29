-- Prove2me | Definitions.Def_TSPHeuristics_Insertion_InsertionMethod
-- name    : TSPHeuristics_Insertion_InsertionMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:30:52.126597+00:00
-- url     : https://prove2.me/theorems/3a557553-4fd9-49d6-b6f7-11ea7bcc0b2c
-- title:
--   TOUR(T, k), COST(T, k) and insertion method runs
-- statement:
--   Let $T$ be a subtour and $k$ a node not in $T$.
--
--   1. **Inserting $k$ into $T$** (p. 570): if $T$ has at least two nodes, choose an edge $(x,y)$ of $T$ minimizing
--   $$d(x,k)+d(k,y)-d(x,y),\tag{3.1}$$
--   delete $(x,y)$ and add $(x,k)$ and $(k,y)$; if $T$ is a single node $i$, the result is the two-node tour $(i,k),(k,i)$. Any subtour obtained this way is a $\mathrm{TOUR}(T,k)$; ties between minimizing edges may be broken arbitrarily.
--   2. **$\mathrm{COST}(T,k)$** (p. 571) is the length of $\mathrm{TOUR}(T,k)$ minus the length of $T$, i.e. the least increase in length over all ways of splicing $k$ into $T$.
--   3. An **insertion method run** (p. 571) on a graph with $n$ nodes is a sequence of subtours $T_1,\dots,T_n$ and nodes $a_0,\dots,a_{n-1}$ with $T_1=[a_0]$ and, for every $1\le i<n$, $a_i\notin T_i$ and
--   $$T_{i+1}=\mathrm{TOUR}(T_i,a_i).\tag{3.2}$$
--   The tour $T_n$ is the approximation; its length is INSERT. No rule for choosing the $a_i$ is imposed.
--
--   These are the objects of Theorem 3, which holds for every insertion method regardless of how the nodes $a_i$ are selected.
--
--   **Formalization Note** $\mathrm{TOUR}(T,k)$ is encoded as: $T'$ is the list $T$ with $k$ inserted at some position $0\le pos\le |T|$ such that no other position gives a shorter closed length. Inserting at position $pos$ deletes the edge between the entries at $pos-1$ and $pos$ (positions $0$ and $|T|$ both delete the closing edge), so the length grows by exactly (3.1) and minimizing the length is minimizing (3.1). For a one-node list both positions give the two-node tour. $\mathrm{COST}(T,k)$ is the minimum over all positions of the length increase. The paper's 1-based subtour index is kept.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 570, §3, definition of TOUR(T, k) and (3.1); p. 571, definitions of insertion method, (3.2), and COST(T, k)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel

namespace TSPHeuristics.Insertion

/-- `T'` is a possible `TOUR(T, k)` (p. 570): `k` is not in the subtour `T`, and `T'` is obtained
by inserting `k` into `T` at a position that minimizes the length of the resulting tour. For a
subtour with at least two nodes, inserting at position `pos` deletes the edge between the entries
at `pos - 1` and `pos` (cyclically; positions `0` and `T.length` both delete the closing edge), so
the length grows by exactly `d(x, k) + d(k, y) - d(x, y)` of (3.1), and minimizing the length
minimizes (3.1). For a one-node subtour every position gives the two-node tour. Every minimizing
position (every tie-breaking) is allowed. -/
def IsInsertion {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n)
    (T' : List (Fin n)) : Prop :=
  k ∉ T ∧ ∃ pos, pos ≤ T.length ∧ T' = T.insertIdx pos k ∧
    ∀ pos', pos' ≤ T.length → TSPHeuristics.Shared.cycleLength d T' ≤ TSPHeuristics.Shared.cycleLength d (T.insertIdx pos' k)

/-- `COST(T, k)` (p. 571): the length of `TOUR(T, k)` minus the length of `T`, i.e. the least
increase in length over all insertion positions. -/
def insCost {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n) : ℝ :=
  (Finset.range (T.length + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
    (fun pos => TSPHeuristics.Shared.cycleLength d (T.insertIdx pos k) - TSPHeuristics.Shared.cycleLength d T)

/-- An insertion method run (p. 571), with the paper's 1-based subtour index: `T 1` is the
one-node subtour `[a 0]`, and for every `1 ≤ i < n` the node `a i` is not in `T i` and
`T (i + 1)` is a `TOUR(T i, a i)`. The approximation is `T n`. The choice of the nodes `a i` is
arbitrary (no selection rule), as is the choice among minimizing insertion positions. -/
def IsInsertionRun {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) :
    Prop :=
  T 1 = [a 0] ∧ ∀ i, 1 ≤ i → i < n → IsInsertion d (T i) (a i) (T (i + 1))

end TSPHeuristics.Insertion


