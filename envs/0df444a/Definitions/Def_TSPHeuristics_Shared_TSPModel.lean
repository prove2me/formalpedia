-- Prove2me | Definitions.Def_TSPHeuristics_Shared_TSPModel
-- name    : TSPHeuristics_Shared_TSPModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:30:07.684078+00:00
-- url     : https://prove2.me/theorems/240c6f4a-2055-466f-ae33-b3f7afe0afbc
-- title:
--   Traveling salesman graphs, tours, OPTIMAL and the closed length of a subtour
-- statement:
--   This file sets up the model of §1 of Rosenkrantz, Stearns and Lewis (1977) and the length of a subtour from §3.
--
--   1. A **traveling salesman graph** on $n$ nodes is a complete graph with distances $d(i,j)\in\mathbb R$ such that $d(i,j)=d(j,i)$, $d(i,j)\ge 0$ and $d(i,j)+d(j,k)\ge d(i,k)$ (the triangle inequality) for all nodes $i,j,k$.
--   2. A **tour** visits every node exactly once and returns to its first node. Listing the nodes in visiting order as $\tau(0),\dots,\tau(n-1)$, its length is
--   $$\mathrm{len}_d(\tau)=\sum_{k=0}^{n-1} d\bigl(\tau(k),\tau(k+1 \bmod n)\bigr).$$
--   3. **OPTIMAL** is the minimum of $\mathrm{len}_d(\tau)$ over all tours $\tau$.
--   4. A **subtour** is a tour on a subset of the nodes, written as the list $[x_0,\dots,x_{m-1}]$ of its nodes in visiting order. Its length is
--   $$\mathrm{cyc}_d([x_0,\dots,x_{m-1}])=\sum_{r=0}^{m-2} d(x_r,x_{r+1})+d(x_{m-1},x_0).$$
--   A one-node subtour is a tour without edges (length $d(x_0,x_0)=0$), and a two-node subtour $[a,b]$ has length $d(a,b)+d(b,a)$.
--
--   These are the standing objects of the paper. They are shared by three missions of this paper: 02-insertion-log (every insertion method within ⌈lg n⌉ + 1 of optimal, §3, pp. 570–572), 03-nearest-cheapest (nearest and cheapest insertion within 2(1 − 1/n), §4, pp. 572–574) and 04-k-optimal-tight (tightness of 2(1 − 1/n) for nearest/cheapest insertion and k-optimal tours, §4 p. 575–576 and §7 pp. 579–581); the model itself is on pp. 563–564 (§1) and p. 570 (§3, subtours).
--
--   **Formalization Note** Nodes are `Fin n` (0-based; the paper labels nodes $1,\dots,n$). A traveling salesman graph is `IsTSPDist d`: symmetric, nonnegative, triangle inequality, plus the normalization $d(i,i)=0$, which is not in the paper and does not affect any length, since a loop never enters a tour, subtour, tree or insertion cost, and it makes the one-node subtour have length $0$, as p. 570 prescribes ("a one node subset [is] a tour without edges"). OPTIMAL is a minimum (`Finset.inf'`) over the finite, nonempty set of all permutations of `Fin n`, never an `sInf`. The empty list has length $0$.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 563, §1 (traveling salesman graph, tour, optimal tour); p. 564 (OPTIMAL, (1.1)); p. 570, §3 (subtour; "We treat a one node subset as a tour without edges")

import Mathlib

namespace TSPHeuristics.Shared

/-- A traveling salesman graph on the nodes `Fin n` (Rosenkrantz–Stearns–Lewis 1977, §1, p. 563):
the distance `d` is symmetric, nonnegative and satisfies the triangle inequality.
The field `diag` (`d i i = 0`) is not in the paper; it is a normalization, since `d(i, i)` never
enters the length of a tour, a subtour or an insertion cost. -/
structure IsTSPDist {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop where
  symm : ∀ i j, d i j = d j i
  nonneg : ∀ i j, 0 ≤ d i j
  triangle : ∀ i j k, d i k ≤ d i j + d j k
  diag : ∀ i, d i i = 0

/-- The length of the tour that visits `τ 0, τ 1, …, τ (n - 1)` in this order and returns to
`τ 0`: the sum of the lengths of its `n` edges. -/
def tourLength {n : ℕ} (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k, d (τ k) (τ (finRotate n k))

/-- OPTIMAL: the minimal length of a tour, the minimum over all orderings of the nodes (a
nonempty finite set). -/
def optimal {n : ℕ} (d : Fin n → Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (tourLength d)

/-- The length of the closed tour visiting the entries of the list `T` in order and returning to
the first one: `d(T₀, T₁) + ⋯ + d(T_{m-2}, T_{m-1}) + d(T_{m-1}, T₀)`. A one-node list `[a]`
gets `d a a` (which is `0` under `IsTSPDist`, the paper's "tour without edges", p. 570), and a
two-node list `[a, b]` gets `d a b + d b a`, the two-node tour of p. 570. -/
def cycleLength {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) : ℝ :=
  (List.zipWith d T (T.rotate 1)).sum

end TSPHeuristics.Shared


