-- Prove2me | Definitions.Def_CoverModular_lpValue
-- name    : CoverModular_lpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:39.09183+00:00
-- url     : https://prove2.me/theorems/b6f1f1f3-9ed1-47de-a89c-46f0aca944e5
-- title:
--   Second-stage value $f(\mathcal A)$ of a flexibility structure (LP (1)/(3))
-- statement:
--   Fix one scenario: supply nodes $i\in I$ with capacities $c_i$, demand nodes $j\in J$ with demands $d_j$, and unit profits $p_{ij}$. For a flexibility structure $\mathcal A\subseteq I\times J$ (a set of arcs), the **second-stage value** is the optimal value of the linear program
--
--   $$
--   f(\mathcal A)=\max_x\ \sum_{i,j}p_{ij}x_{ij}\quad\text{s.t.}\quad \sum_i x_{ij}\le d_j\ \forall j,\qquad \sum_j x_{ij}\le c_i\ \forall i,\qquad x_{ij}=0\ \text{for }(i,j)\notin\mathcal A,\qquad x\ge0 .
--   $$
--
--   This is the profit-maximizing fulfillment of demand from capacity using only the arcs of $\mathcal A$; the paper's expected profit $F$ averages it over scenarios.
--
--   **Formalization Note** The feasible region is `Transportation.Feasible` of the published definition `BipartiteMatchingHT_Delay_Transportation`, for the network whose edges are the arcs of $\mathcal A$, with supplies $c$ and capacities $d$; flows are curried, $x:I\to J\to\mathbb R$. The maximum is the supremum of the objective values over the feasible set; when $c,d\ge0$ (assumed in every theorem) the set contains $x=0$, is bounded, and the supremum is attained.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §2, display (1), p.6; §3.1, display (3), p.10

import Mathlib
import Definitions.Def_BipartiteMatchingHT_Delay_Transportation

open BipartiteMatchingHT.Delay

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J]

/-- The transportation network of the second-stage LP (3) for a flexibility structure `A`
(DeValve, Pekeč, Wei, SSRN 3844987, §2, display (1), p.6; §3.1, display (3), p.10): supply
node `i` has capacity `c i`, demand node `j` has demand `d j`, and `x i j` may be positive only
on arcs `(i, j) ∈ A`. -/
def network (c : I → ℝ) (d : J → ℝ) (A : Finset (I × J)) : Transportation I J :=
  ⟨fun i j => (i, j) ∈ A, c, d⟩

/-- The profit `∑_{i,j} p_ij x_ij` of a flow `x` (objective of (1)/(3), SSRN 3844987, p.6). -/
noncomputable def profit (p : I → J → ℝ) (x : I → J → ℝ) : ℝ :=
  ∑ i, ∑ j, p i j * x i j

/-- The second-stage value `f(A)` of a flexibility structure `A` in one scenario
(DeValve, Pekeč, Wei, *Approximate submodularity in network design problems*, SSRN 3844987,
§2, display (1), p.6, and §3.1, display (3), p.10):
`f(A) = max_x ∑_{i,j} p_ij x_ij` s.t. `∑_i x_ij ≤ d_j` for all `j`, `∑_j x_ij ≤ c_i` for all
`i`, `x_ij = 0` for `(i, j) ∉ A`, `x ≥ 0`.

**Formalization Note** The feasible region is `Transportation.Feasible` of the published
definition `BipartiteMatchingHT_Delay_Transportation` for the network with edge relation
`(i, j) ∈ A`, supplies `c` and capacities `d`. Flows are curried, `x : I → J → ℝ`, and an arc is
a pair `(i, j) : I × J`. The `max` is written as `sSup` of the set of objective values; when
`c, d ≥ 0` (the standing assumptions of every theorem of the mission) the region contains
`x = 0`, is bounded, and the supremum is attained, so `sSup` is the paper's maximum and not a
junk value. -/
noncomputable def lpValue (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ) (A : Finset (I × J)) : ℝ :=
  sSup (profit p '' {x | (network c d A).Feasible x})

end CoverModular


