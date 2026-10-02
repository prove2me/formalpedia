-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_FTildeR
-- name    : DiscreteConvex_ConjugacyDualityD_FTildeR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:05:23.942933+00:00
-- url     : https://prove2.me/theorems/4efbf6de-e908-4446-9801-4c8967301718
-- title:
--   FTildeR
-- statement:
--   The dual-of-dual optimal value $\tilde f(x)=\sup_y\tilde K_r(x,y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.70).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.70)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KTildeR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The dual-of-dual optimal value `f̃(x) = sup_y K̃r(x,y)`, Eq. (8.70). -/
noncomputable def FTildeR (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x : V → ℤ) : EReal :=
  sSup {t : EReal | ∃ y : V → ℤ, t = KTildeR c r B x y}

end DiscreteConvex.ConjugacyDualityD


