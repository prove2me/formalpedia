-- Prove2me | Definitions.Def_LearnManip_LambdaStar
-- name    : LearnManip_LambdaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:52.117836+00:00
-- url     : https://prove2.me/theorems/31128d73-829b-4b26-83d6-625deaaf83cb
-- title:
--   Optimal distortion rule $\Lambda^*$
-- statement:
--   The optimal distortion rule, as a function of the value $y$ of the posterior mean:
--   $$\Lambda^*(\mu,s,c)(y)=\exp\Bigl(\frac{y-\mu}{\gamma(1-\alpha)}-\frac12\,\frac{(s-s_{TH}(c))^+}{\gamma^2(1-\alpha)^2}\Bigr).$$
--
--   **Formalization Note.** That $(s-s_{TH}(c))^+$ is the variance of $\mu^{q^*}$ is a clause of the goal, not part of this definition.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (19), p.17, and the end of the proof of Theorem 2, p.35

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_sTH

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The optimal distortion rule (19), p.17, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04):
`Λ*(μ, s, c)(y) = exp((y − μ)/(γ(1−α)) − (1/2)(s − s_TH(c))⁺/(γ²(1−α)²))`, the paper's `σ²` being
`(s − s_TH(c))⁺`.

**Formalization Note.** The subtraction is in `ℝ≥0`, so it is the positive part. That this is the
variance of `μ^{q*}` is a clause of `theorem_2`, not of this definition. -/
noncomputable def LambdaStar (P : Params) (μ : ℝ) (s c : ℝ≥0) (y : ℝ) : ℝ :=
  Real.exp ((y - μ) / ((P.γ : ℝ) * (1 - (P.α : ℝ)))
    - (1 / 2) * ((s - sTH P c : ℝ≥0) : ℝ) / ((P.γ : ℝ) ^ 2 * (1 - (P.α : ℝ)) ^ 2))

end LearnManip


