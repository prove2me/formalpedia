-- Prove2me | Definitions.Def_TentNoise_Dnoise
-- name    : TentNoise_Dnoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:38.046099+00:00
-- url     : https://prove2.me/theorems/0c6baae6-b2f0-4875-8dc8-7deed07a24bc
-- title:
--   Mean reflected-Gaussian displacement $D(\sigma)$
-- statement:
--   The **mean displacement** of one reflected Gaussian step started from the uniform law is
--
--   $$
--   D(\sigma)=\int_0^1\mathbb E\,\bigl|\mathfrak r(a+\sigma Z)-a\bigr|\,da,\qquad Z\sim\mathcal N(0,1).
--   $$
--
--   It is the expected size of the noise increment; Lemma B.8 shows $D(\sigma)\ge d_0\min\{\sigma,1\}$, which detects large noise levels.
--
--   **Formalization Note** Both integrals are Bochner integrals of functions bounded by $1$, so they are integrable and no default value occurs.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.8, p.31 (PDF p.31)

import Mathlib
import Definitions.Def_TentNoise_refl
import Definitions.Def_TentNoise_unifI

open MeasureTheory ProbabilityTheory

namespace TentNoise

/-- The mean displacement of one reflected Gaussian step,
`D(σ) = ∫₀¹ E|𝔯(a + σZ) − a| da`, `Z ∼ N(0, 1)` (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.8, p.31).

**Formalization Note** Both integrals are Bochner integrals of functions bounded by `1`
(`𝔯 ∈ [0,1]` and `a ∈ [0,1]`), so they are integrable and no default value is used. -/
noncomputable def Dnoise (σ : ℝ) : ℝ :=
  ∫ a, (∫ z, |refl (a + σ * z) - a| ∂(gaussianReal 0 1)) ∂unifI

end TentNoise


