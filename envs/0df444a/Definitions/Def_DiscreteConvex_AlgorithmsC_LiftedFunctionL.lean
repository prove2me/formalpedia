-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_LiftedFunctionL
-- name    : DiscreteConvex_AlgorithmsC_LiftedFunctionL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:34.372455+00:00
-- url     : https://prove2.me/theorems/44fa7c82-497e-4d94-b3e7-363cf41dae14
-- title:
--   LiftedFunctionL
-- statement:
--   The lift $\tilde g(p_0,p)=g(p-p_0\mathbf 1)$ of $g$ to `Option W`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178/307, Eq. (7.2)/(10.35), redeclared, generic ground type.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178/307, Eq. (7.2)/(10.35), redeclared, generic ground type

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift `g̃(p0,p) = g(p - p0·1)` of `g` to `Option V` (Eq. (7.2)/(10.35)). -/
def LiftedFunctionL {W : Type*} [Fintype W] [DecidableEq W] (g : (W → ℤ) → WithTop ℝ) :
    (Option W → ℤ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.AlgorithmsC


