-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_F0
-- name    : DiscreteConvex_ConjugacyDualityD_F0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:19.700835+00:00
-- url     : https://prove2.me/theorems/4f6776de-97c4-4315-9f4a-91994391ea22
-- title:
--   F0
-- statement:
--   The perturbation $F_0(x,u)=c(x)+\delta_B(x+u)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.62).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.62)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IndicatorWT

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The perturbation `F0(x,u) = c(x) + δ_B(x+u)`, Eq. (8.62). -/
noncomputable def F0 (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x u : V → ℤ) : WithTop ℝ :=
  c x + IndicatorWT B (fun v => x v + u v)

end DiscreteConvex.ConjugacyDualityD


