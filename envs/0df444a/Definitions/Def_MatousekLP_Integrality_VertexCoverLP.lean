-- Prove2me | Definitions.Def_MatousekLP_Integrality_VertexCoverLP
-- name    : MatousekLP_Integrality_VertexCoverLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:17:25.238996+00:00
-- url     : https://prove2.me/theorems/251de0dc-c0fe-472d-80ac-662cbde05ad7
-- title:
--   The vertex-cover LP relaxation (3.3) and its optimal solutions
-- statement:
--   Let $G = (V, E)$ be a finite simple graph. The LP relaxation (3.3) of the minimum vertex cover problem is
--   $$
--   \text{minimize } \sum_{v \in V} x_v \quad \text{subject to } x_u + x_v \ge 1 \text{ for every edge } \{u, v\} \in E, \quad 0 \le x_v \le 1 \text{ for all } v \in V .
--   $$
--   A vector $x \in \mathbb{R}^V$ is **feasible** for (3.3) if it satisfies these constraints, and it is an **optimal solution** if it is feasible and $\sum_v x_v \le \sum_v y_v$ for every feasible $y$.
--
--   Replacing $0 \le x_v \le 1$ by $x_v \in \{0,1\}$ gives the integer program (3.2), whose feasible solutions are the indicator vectors of vertex covers.
--
--   **Formalization Note** Optimality is stated against every feasible point, not via an infimum.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 37, LP relaxation (3.3)

import Mathlib

namespace MatousekLP.Integrality

/-- Feasibility for the LP relaxation (3.3) of the vertex-cover integer program (p. 37):
`x = (x_v)_{v ∈ V}` with `x_u + x_v ≥ 1` for every edge `{u, v}` and `0 ≤ x_v ≤ 1`
for every vertex. -/
def IsVCRelaxFeasible {V : Type*} (G : SimpleGraph V) (x : V → ℝ) : Prop :=
  (∀ u v : V, G.Adj u v → 1 ≤ x u + x v) ∧ ∀ v : V, 0 ≤ x v ∧ x v ≤ 1

/-- `x` is an optimal solution of the LP relaxation (3.3), `minimize ∑_v x_v`:
it is feasible and `∑_v x_v ≤ ∑_v y_v` for every feasible `y`. -/
def IsVCRelaxOptimal {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V → ℝ) : Prop :=
  IsVCRelaxFeasible G x ∧ ∀ y : V → ℝ, IsVCRelaxFeasible G y → ∑ v, x v ≤ ∑ v, y v

end MatousekLP.Integrality


