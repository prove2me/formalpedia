-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiR
-- name    : DiscreteConvex_ConjugacyDualityD_PhiR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:00:14.713527+00:00
-- url     : https://prove2.me/theorems/5b37691f-7280-4ec1-83be-ec7d529ce6aa
-- title:
--   PhiR
-- statement:
--   The $r$-regularized optimal-value function $\varphi_r(u)=\inf_x F_r(x,u)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.63).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.63)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `r`-regularized optimal value function `φr(u) = inf_x Fr(x,u)`, Eq. (8.63). -/
noncomputable def PhiR (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (u : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ x : V → ℤ, t = ToEReal (Fr c r B x u)}

end DiscreteConvex.ConjugacyDualityD


