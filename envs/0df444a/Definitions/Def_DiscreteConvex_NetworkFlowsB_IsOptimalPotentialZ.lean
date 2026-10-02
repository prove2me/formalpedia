-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotentialZ
-- name    : DiscreteConvex_NetworkFlowsB_IsOptimalPotentialZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:37.474435+00:00
-- url     : https://prove2.me/theorems/da4a3792-27ed-4b20-ae65-066ad6bf713f
-- title:
--   IsOptimalPotentialZ
-- statement:
--   $p$ is an optimal potential for the integer flow $\xi$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, condition (POT) of Theorem 9.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, condition (POT) of Theorem 9.16

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMin
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedArcCostZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedBoundaryCostZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `p` is an optimal potential for the integer flow `ξ`. -/
def IsOptimalPotentialZ (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ)
    (xi : A → ℤ) (p : V → ℝ) : Prop :=
  (∀ a : A, xi a ∈ ArgMinArcZ (ReducedArcCostZ tail head fa p a)) ∧
    BoundaryZ tail head xi ∈ ArgMin (ReducedBoundaryCostZ f p)

end DiscreteConvex.NetworkFlowsB


