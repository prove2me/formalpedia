-- Prove2me | Definitions.Def_CPDETrial_postMean
-- name    : CPDETrial_postMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:47:03.16775+00:00
-- url     : https://prove2.me/theorems/37cf902f-9c62-427a-a5f7-868e63222eba
-- title:
--   Posterior mean $\mu^t$ along allocations and observations
-- statement:
--   Given the prior $(\mu^0,\Sigma^0)$, the sampling variances $\lambda$, an allocation sequence $(u^t)$ and observations $(y_t)$, the posterior means are defined by $\mu^0$ and
--
--   $$
--   \mu^{t+1} = \mu^t + \frac{y_t-\mu^t_{u^t}}{\lambda_{u^t}+\Sigma^t_{u^t,u^t}}\,\Sigma^t e_{u^t},
--   $$
--
--   with $\Sigma^t$ the posterior covariances. Here $y_t$ is the observation $Y^{t+1}_{u^t}$ of patient $t+1$, the one that follows the allocation $u^t$.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 6 (§1.3) and p. 9, eq. (8)

import Mathlib
import Definitions.Def_CPDETrial_postMeanStep
import Definitions.Def_CPDETrial_postCov
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Posterior mean along an allocation and observation sequence** (eq. (8), iterated).
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §1.3 (p. 6) and §3.1, eq. (8) (p. 9).

Given the prior `(mu0, Sig0) = (µ⁰, Σ⁰)`, the sampling variances `lam`, an allocation sequence
`u` and an observation sequence `y`, `postMean mu0 Sig0 lam u y t` is `µ^t`: `µ^0 = µ⁰` and
`µ^{t+1}` is the one-observation update (8) of `(µ^t, Σ^t)` for arm `u t` with observed value
`y t`.

**Formalization Note.** Index convention: `y t` is the observation `Y^{t+1}_{u^t}` of patient
`t + 1`, the one that follows the allocation `u t` (p. 6: "After an action `u^t` … is chosen,
the observation `Y^{t+1}_{u^t}` is realized before the next period's decision"). -/
noncomputable def postMean {M : ℕ} (mu0 : Fin M → ℝ) (Sig0 : Matrix (Fin M) (Fin M) ℝ)
    (lam : Fin M → ℝ≥0) (u : ℕ → Fin M) (y : ℕ → ℝ) : ℕ → Fin M → ℝ
  | 0 => mu0
  | t + 1 => postMeanStep lam (postMean mu0 Sig0 lam u y t) (postCov Sig0 lam u t) (u t) (y t)

end CPDETrial


