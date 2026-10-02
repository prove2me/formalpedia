-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunction
-- name    : DiscreteConvex_NetworkFlowsC_LiftedFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:46.722987+00:00
-- url     : https://prove2.me/theorems/8dcbe412-89b8-42ef-998f-221e545a94e0
-- title:
--   LiftedFunction
-- statement:
--   The lift of $f$ to $\tilde V=\{0\}\cup V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The lift of `f` to `Ṽ = {0}∪V`. -/
def LiftedFunction (f : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.NetworkFlowsC


