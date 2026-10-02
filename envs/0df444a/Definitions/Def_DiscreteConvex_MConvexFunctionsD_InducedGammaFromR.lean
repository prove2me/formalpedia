-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_InducedGammaFromR
-- name    : DiscreteConvex_MConvexFunctionsD_InducedGammaFromR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:51:01.300486+00:00
-- url     : https://prove2.me/theorems/84467575-f914-499f-8770-b6d8848940f4
-- title:
--   InducedGammaFromR
-- statement:
--   The distance function $\gamma_f(u,v)=f(\chi_v-\chi_u)$ induced by a positively homogeneous real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (6.81).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (6.81)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The distance function `γ_f(u,v) = f(χv-χu)` induced by a positively homogeneous real-domain
function, Eq. (6.81). -/
def InducedGammaFromR (f : (V → ℝ) → WithTop ℝ) (u v : V) : WithTop ℝ :=
  f (fun w => (CharVec v w - CharVec u w : ℝ))

end DiscreteConvex.MConvexFunctionsD


