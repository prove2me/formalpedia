-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunctionRL
-- name    : DiscreteConvex_NetworkFlowsC_LiftedFunctionRL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:00.509662+00:00
-- url     : https://prove2.me/theorems/42059ad0-7442-48fc-8d49-3acf777688ab
-- title:
--   LiftedFunctionRL
-- statement:
--   The lift of $g$ to $\tilde V$, L-side convention, real domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared, real version

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def LiftedFunctionRL (g : (V → ℝ) → WithTop ℝ) : (Option V → ℝ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.NetworkFlowsC


