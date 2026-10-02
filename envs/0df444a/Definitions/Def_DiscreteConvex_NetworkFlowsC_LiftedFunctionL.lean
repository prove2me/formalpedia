-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunctionL
-- name    : DiscreteConvex_NetworkFlowsC_LiftedFunctionL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:59.147384+00:00
-- url     : https://prove2.me/theorems/db520b5e-5388-4a83-8d6f-28f6e80f7b85
-- title:
--   LiftedFunctionL
-- statement:
--   The lift of $g$ to $\tilde V$, L-side convention.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def LiftedFunctionL (g : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.NetworkFlowsC


