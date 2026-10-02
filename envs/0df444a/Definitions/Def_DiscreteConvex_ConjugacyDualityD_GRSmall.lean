-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall
-- name    : DiscreteConvex_ConjugacyDualityD_GRSmall
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:02:12.058424+00:00
-- url     : https://prove2.me/theorems/f04416f5-f2d9-4326-90ea-81191d5d72cd
-- title:
--   GRSmall
-- statement:
--   The $r$-regularized dual objective $g_r(y)=\inf_x K_r(x,y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.65).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.65)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `r`-regularized dual objective `gr(y) = inf_x Kr(x,y)`, Eq. (8.65). -/
noncomputable def GRSmall (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (y : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ x : V → ℤ, t = KR c r B x y}

end DiscreteConvex.ConjugacyDualityD


