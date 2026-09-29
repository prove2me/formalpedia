-- Prove2me | Definitions.Def_TSPHeuristics_NNLower_TSPModel
-- name    : TSPHeuristics_NNLower_TSPModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:22:47.855486+00:00
-- url     : https://prove2.me/theorems/d42cb102-1c8c-4e02-9565-2eed8d06b2d7
-- title:
--   Traveling salesman graphs, tours, OPTIMAL and nearest-neighbor tours
-- statement:
--   This file sets up the model of §1 and §2 of Rosenkrantz, Stearns and Lewis (1977).
--
--   1. A **traveling salesman graph** on $n$ nodes is a complete graph with a distance $d(i,j)\in\mathbb R$ such that $d(i,j)=d(j,i)$, $d(i,j)\ge 0$ and $d(i,j)+d(j,k)\ge d(i,k)$ (the triangle inequality) for all nodes $i,j,k$.
--   2. A **tour** visits every node exactly once and returns to its first node. Listing the nodes in visiting order as $\tau(0),\tau(1),\dots,\tau(n-1)$, its length is
--   $$\mathrm{len}_d(\tau)=\sum_{k=0}^{n-1} d\bigl(\tau(k),\tau(k+1 \bmod n)\bigr).$$
--   3. **OPTIMAL** is the minimum of $\mathrm{len}_d(\tau)$ over all tours $\tau$.
--   4. A tour $\tau$ is a **nearest-neighbor tour** if it can be produced by the nearest neighbor algorithm: start at the arbitrary node $\tau(0)$; at step $k$ go from the last node added, $\tau(k)$, to a node $\tau(k+1)$ that is at least as close to $\tau(k)$ as every node not yet on the path; after all nodes are added, return to $\tau(0)$. Ties are broken arbitrarily. The length of such a tour is the paper's NEARNEIBER.
--
--   These are the objects in which Theorem 2 is stated.
--
--   **Formalization Note** Nodes are `Fin n` and a tour is a permutation `τ` of `Fin n`. The structure `IsTSPDist` has a fourth field `d i i = 0` that is not in the paper; it is a normalization, because $d(i,i)$ never enters the length of a tour. OPTIMAL is a minimum (`Finset.inf'`) over the finite, nonempty set of all permutations.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 563, §1 (definition of a traveling salesman graph, tour, optimal tour); p. 564 (OPTIMAL); pp. 564–565, §2 (nearest neighbor algorithm)

import Mathlib

namespace TSPHeuristics.NNLower

/-- A traveling salesman graph on the nodes `Fin n` (Rosenkrantz–Stearns–Lewis 1977, §1, p. 563):
the distance `d` is symmetric, nonnegative and satisfies the triangle inequality.
The field `diag` (`d i i = 0`) is not in the paper; it is a normalization, since a distance
`d(i, i)` never enters the length of a tour. -/
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

/-- `τ` is a tour the nearest neighbor algorithm (p. 564) can produce: starting from `τ 0`, each
step goes from the node `τ k` last added to a node `τ (k + 1)` that is at least as close to `τ k`
as every node not yet on the path. The start node and the resolution of ties are arbitrary. -/
def IsNearestNeighborTour {n : ℕ} (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k j : Fin n, k.val + 1 < n → (∀ l, l ≤ k → τ l ≠ j) →
    d (τ k) (τ (finRotate n k)) ≤ d (τ k) j

end TSPHeuristics.NNLower


