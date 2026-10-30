-- Prove2me | Definitions.Def_CPDETrial_postMeanStep
-- name    : CPDETrial_postMeanStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:45:57.427986+00:00
-- url     : https://prove2.me/theorems/bbab0e93-9d59-4d35-8ffa-7bb5cb742a95
-- title:
--   One-observation posterior mean update (eq. (8), $\tau=1$)
-- statement:
--   Let $(\mu,\Sigma)$ be the current mean and covariance of the Gaussian belief about the arm means, and let $\lambda_i>0$ be the sampling variance of arm $i$. After observing the value $y$ from arm $i$, the posterior mean is
--
--   $$
--   \mu' = \mu + \frac{y-\mu_i}{\lambda_i+\Sigma_{i,i}}\,\Sigma e_i ,
--   $$
--
--   that is, every arm's mean moves in proportion to its covariance $\Sigma_{a,i}$ with the sampled arm. This is eq. (8) of the paper with $\tau=1$.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 9, eq. (8) with τ = 1

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **One-observation posterior mean update, eq. (8) with `τ = 1`.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §3.1, eq. (8), p. 9: "`µ^{t+τ} = µ^t + (Ȳ^τ_i − µ^t_i)/(λ_i/τ + Σ^t_{i,i}) Σ^t e_i`".

`postMeanStep lam m S i y` is the mean `µ^{t+1}` after observing the value `y` from arm `i`,
when the current belief is `(m, S) = (µ^t, Σ^t)`: `m + ((y − m_i)/(λ_i + S_ii)) · S e_i`
(`S e_i` is the `i`-th column of `S`).

**Formalization Note.** As for `postCovStep`, the denominator `λ_i + S_ii` is positive whenever
the formula is used (`λ_i > 0`, `S_ii ≥ 0`); Lean's `x / 0 = 0` never applies. -/
noncomputable def postMeanStep {M : ℕ} (lam : Fin M → ℝ≥0) (m : Fin M → ℝ)
    (S : Matrix (Fin M) (Fin M) ℝ) (i : Fin M) (y : ℝ) : Fin M → ℝ :=
  m + ((y - m i) / ((lam i : ℝ) + S i i)) • (fun a => S a i)

end CPDETrial


