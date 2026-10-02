-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr
-- name    : DiscreteConvex_ConjugacyDualityD_Fr
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:59:26.734189+00:00
-- url     : https://prove2.me/theorems/cb8252c3-fa92-47b2-9b47-972ab41395ec
-- title:
--   Fr
-- statement:
--   The perturbation $F_r(x,u)=F_0(x,u)+r(u)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.61).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.61)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_F0

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The perturbation `Fr(x,u) = F0(x,u) + r(u)`, Eq. (8.61). -/
noncomputable def Fr (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x u : V → ℤ) : WithTop ℝ :=
  F0 c B x u + r u

end DiscreteConvex.ConjugacyDualityD


