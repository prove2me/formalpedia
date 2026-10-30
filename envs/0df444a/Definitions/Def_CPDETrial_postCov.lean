-- Prove2me | Definitions.Def_CPDETrial_postCov
-- name    : CPDETrial_postCov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:46:29.645479+00:00
-- url     : https://prove2.me/theorems/0b1aa8d3-39cd-4eaf-beda-ced6df15a675
-- title:
--   Posterior covariance $\Sigma^t$ along an allocation sequence
-- statement:
--   Given the prior covariance $\Sigma^0$, the sampling variances $\lambda$, and an allocation sequence $u^0,u^1,\dots$ (arm $u^t$ is given to patient $t+1$), the posterior covariances are defined recursively by $\Sigma^0$ and
--
--   $$
--   \Sigma^{t+1} = \Sigma^t - \frac{\Sigma^t e_{u^t} e_{u^t}^{\top}\Sigma^t}{\lambda_{u^t}+\Sigma^t_{u^t,u^t}} .
--   $$
--
--   They do not depend on the observed values. Together with the posterior mean this is the belief state $(\mu^t,\Sigma^t)$ on which all allocation indices of the paper are evaluated.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 6 (§1.3) and p. 9, eq. (8)

import Mathlib
import Definitions.Def_CPDETrial_postCovStep
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Posterior covariance along an allocation sequence** (eq. (8), iterated).
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §1.3 (p. 6) and §3.1, eq. (8) (p. 9).

Given the prior covariance `Sig0 = Σ⁰`, the sampling variances `lam` and an allocation sequence
`u : ℕ → Fin M` (`u t` is the arm `u^t` given to patient `t + 1`), `postCov Sig0 lam u t` is
`Σ^t`: `Σ^0 = Σ⁰` and `Σ^{t+1}` is the one-observation update (8) of `Σ^t` for arm `u t`.
The covariance does not depend on the observed values. -/
noncomputable def postCov {M : ℕ} (Sig0 : Matrix (Fin M) (Fin M) ℝ) (lam : Fin M → ℝ≥0)
    (u : ℕ → Fin M) : ℕ → Matrix (Fin M) (Fin M) ℝ
  | 0 => Sig0
  | t + 1 => postCovStep lam (postCov Sig0 lam u t) (u t)

end CPDETrial


