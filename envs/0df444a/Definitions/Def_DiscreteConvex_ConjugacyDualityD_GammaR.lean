-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_GammaR
-- name    : DiscreteConvex_ConjugacyDualityD_GammaR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:03:49.374847+00:00
-- url     : https://prove2.me/theorems/5c6e1aa4-af8b-476b-bcb5-745819b988bc
-- title:
--   GammaR
-- statement:
--   The dual optimal-value function $\gamma_r(v)=\sup_y G_r(y,v)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.68).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.68)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRBig

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The dual optimal value function `γr(v) = sup_y Gr(y,v)`, Eq. (8.68). -/
noncomputable def GammaR (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (v : V → ℤ) : EReal :=
  sSup {t : EReal | ∃ y : V → ℤ, t = GRBig c r B y v}

end DiscreteConvex.ConjugacyDualityD


