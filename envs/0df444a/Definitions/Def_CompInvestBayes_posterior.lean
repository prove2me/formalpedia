-- Prove2me | Definitions.Def_CompInvestBayes_posterior
-- name    : CompInvestBayes_posterior
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:25.672976+00:00
-- url     : https://prove2.me/theorems/57c4225e-22f9-4792-8414-83b526bee612
-- title:
--   Posterior belief $\pi_t$ in Bayes-formula form
-- statement:
--   Let $m_1=\min(S_1,\mu_H)$ and $m_0=\min(S_1,\mu_L)$ be the drifts of $X^s_1$ in the favorable and unfavorable market. With the likelihood ratio
--
--   $$
--   L_t=\exp\Big(\frac{(m_1-m_0)X^s_{1,t}}{\sigma^2}-\frac{(m_1^2-m_0^2)\,t}{2\sigma^2}\Big),
--   $$
--
--   the follower's posterior belief is
--
--   $$
--   \pi_t=\frac{y_0L_t}{y_0L_t+1-y_0}.
--   $$
--
--   The paper defines $\pi_t=\mathbb P(\theta=1\mid\mathcal F^{X^s_1}_t)$; the milestone *posterior belief* states that this process is a version of that conditional probability. For $S_1\le\mu_L$, $m_1=m_0$ and $\pi_t=y_0$ (Remark 1).
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), definition of π_t, p.9 (PDF 9)

import Mathlib
import Definitions.Def_CompInvestBayes_obsFiltration

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The follower's posterior belief** `π_t = P(θ = 1 | F^{X^s_1}_t)` (SSRN 3408260, p.9, PDF 9),
in its Bayes-formula version. With `m₁ := min(S₁, µ_H)`, `m₀ := min(S₁, µ_L)` (the drifts of
`X^s_1` under `θ = 1` and `θ = 0`) and the likelihood ratio

`L_t := exp( (m₁ − m₀) X^s_{1,t} / σ² − (m₁² − m₀²) t / (2σ²) )`,

the posterior is `π_t := y₀ L_t / (y₀ L_t + 1 − y₀)`.

**Formalization Note.** The paper defines `π_t` as a conditional probability; this is the continuous
version given by Bayes' formula. The milestone `posterior_eq_condExp` states that it is a version of
`P(θ = 1 | F^{X^s_1}_t)`. For `S₁ ≤ µ_L` (including `S₁ = 0`) `m₁ = m₀`, so `π_t = y₀` (Remark 1). -/
noncomputable def posterior (p : Params) (σ : ℝ) (E : Setup Ω) (S1 y0 : ℝ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  let m1 := min S1 p.muH
  let m0 := min S1 p.muL
  let L := Real.exp ((m1 - m0) * obsProcess p σ E S1 y0 t ω / σ ^ 2
    - (m1 ^ 2 - m0 ^ 2) * (t : ℝ) / (2 * σ ^ 2))
  y0 * L / (y0 * L + (1 - y0))

end CompInvestBayes


