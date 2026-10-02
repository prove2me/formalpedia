-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedBoundaryCostZ
-- name    : DiscreteConvex_NetworkFlowsB_ReducedBoundaryCostZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:46.974127+00:00
-- url     : https://prove2.me/theorems/3ae023ba-6a41-4e27-aa26-b4966524c641
-- title:
--   ReducedBoundaryCostZ
-- statement:
--   The reduced boundary cost, integer domain, real potential.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Eq. (9.69)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Eq. (9.69)-adjacent

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The reduced boundary cost, integer domain, real potential. -/
def ReducedBoundaryCostZ (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (x : V → ℤ) : WithTop ℝ :=
  f x - ((∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB


