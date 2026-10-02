-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_GGen
-- name    : DiscreteConvex_ConjugacyDualityD_GGen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:59:29.651705+00:00
-- url     : https://prove2.me/theorems/627bb586-45f6-4aec-9de7-7d5753460bdd
-- title:
--   GGen
-- statement:
--   The general dual objective $g(y)=\inf_x K(x,y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.60).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.60)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KGen

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The general dual objective `g(y) = inf_x K(x,y)`, Eq. (8.60). -/
noncomputable def GGen (F : (V → ℤ) → (V → ℤ) → WithTop ℝ) (y : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ x : V → ℤ, t = KGen F x y}

end DiscreteConvex.ConjugacyDualityD


