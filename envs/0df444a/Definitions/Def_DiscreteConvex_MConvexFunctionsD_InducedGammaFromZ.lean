-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_InducedGammaFromZ
-- name    : DiscreteConvex_MConvexFunctionsD_InducedGammaFromZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:51:10.438994+00:00
-- url     : https://prove2.me/theorems/7d597407-434c-431c-8de3-fc6c126df547
-- title:
--   InducedGammaFromZ
-- statement:
--   The distance function $\gamma_f(u,v)=f(\chi_v-\chi_u)$ induced by a positively homogeneous integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (6.81)-analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (6.81)-analogue

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The distance function `γ_f(u,v) = f(χv-χu)` induced by a positively homogeneous
integer-domain function. -/
def InducedGammaFromZ (f : (V → ℤ) → WithTop ℝ) (u v : V) : WithTop ℝ :=
  f (fun w => CharVec v w - CharVec u w)

end DiscreteConvex.MConvexFunctionsD


