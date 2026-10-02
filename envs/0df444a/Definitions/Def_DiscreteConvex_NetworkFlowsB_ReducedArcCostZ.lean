-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedArcCostZ
-- name    : DiscreteConvex_NetworkFlowsB_ReducedArcCostZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:58.698418+00:00
-- url     : https://prove2.me/theorems/b67d1f01-7b95-4746-8830-e0418abcc856
-- title:
--   ReducedArcCostZ
-- statement:
--   The reduced arc cost, integer flow, real potential.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Eq. (9.68)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Eq. (9.68)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Coboundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The reduced arc cost, integer flow, real potential. -/
def ReducedArcCostZ (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (p : V → ℝ) (a : A) (t : ℤ) :
    WithTop ℝ :=
  fa a t + ((Coboundary tail head p a * (t : ℝ) : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB


