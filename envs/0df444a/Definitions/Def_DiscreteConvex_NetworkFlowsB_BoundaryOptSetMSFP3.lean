-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryOptSetMSFP3
-- name    : DiscreteConvex_NetworkFlowsB_BoundaryOptSetMSFP3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:27:10.16644+00:00
-- url     : https://prove2.me/theorems/8a0e22c5-a2b2-4f51-84ff-36fa094957e9
-- title:
--   BoundaryOptSetMSFP3
-- statement:
--   The set of boundaries of optimal flows for MSFP3, $\partial\Xi^*=\{\partial\xi:\xi\text{ optimal}\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of boundaries of optimal flows for MSFP3, `∂Ξ* = {∂ξ | ξ optimal}`. -/
def BoundaryOptSetMSFP3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ) :
    Set (V → ℝ) :=
  {x | ∃ xi, OptimalFlowMCFP3 tail head fa f xi ∧ x = Boundary tail head xi}

end DiscreteConvex.NetworkFlowsB


