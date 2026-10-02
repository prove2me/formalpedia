-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_GammaHat
-- name    : DiscreteConvex_MConvexFunctionsD_GammaHat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:51:17.024136+00:00
-- url     : https://prove2.me/theorems/46c3cc80-0ccb-4028-803b-4736cfdecdda
-- title:
--   GammaHat
-- statement:
--   The extension $\hat\gamma(x)$ of a distance function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Eq. (6.82).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Eq. (6.82)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The extension `γ̂(x)` of a distance function, Eq. (6.82). -/
noncomputable def GammaHat (γ : V → V → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ lam : V → V → ℝ, (∀ u v, 0 ≤ lam u v) ∧
    (∀ w, x w = ∑ u, ∑ v, lam u v * (CharVec v w - CharVec u w : ℝ)) ∧
    L = ∑ u, ∑ v, PosScalarMul (lam u v) (γ u v)}

end DiscreteConvex.MConvexFunctionsD


