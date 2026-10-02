-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRhoZ
-- name    : DiscreteConvex_LConvexFunctionsD_InducedRhoZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:12.707442+00:00
-- url     : https://prove2.me/theorems/34deb966-9e3a-433b-be76-5ec7a6ae0844
-- title:
--   InducedRhoZ
-- statement:
--   The set function $\rho_g(X)=g(\chi_X)$ induced by a positively homogeneous integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Eq. (7.35)-analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Eq. (7.35)-analogue

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IndicatorVec

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The set function `ρ_g(X) = g(χ_X)` induced by a positively homogeneous integer-domain
function. -/
def InducedRhoZ (g : (V → ℤ) → WithTop ℝ) (X : Finset V) : WithTop ℝ := g (IndicatorVec X)

end DiscreteConvex.LConvexFunctionsD


