-- Prove2me | Definitions.Def_PhiSobBayes_posterior
-- name    : PhiSobBayes_posterior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:22.662063+00:00
-- url     : https://prove2.me/theorems/feada170-bd2a-421d-8080-3826f3ceb413
-- title:
--   Posterior $\mu_{t,y}=\mathcal L(X\mid Y_t=y)$ by Bayes' formula (44)
-- statement:
--   For a prior $\mu$ on $\mathbb R^n$, a signal-to-noise ratio $t$ and an observation $y\in\mathbb R^n$, the **posterior** of the Gaussian additive model is
--   $$\mu_{t,y}(dx)=\frac{e^{-\|y-\sqrt t\,x\|_2^2/2}\,\mu(dx)}{\int e^{-\|y-\sqrt t\,x'\|_2^2/2}\,\mu(dx')}.\tag{44}$$
--
--   It is the conditional law of $X$ given $Y_t=y$. Its mean $m(y)=\mathbb E_{\mu_{t,y}}f$ is the optimal estimator in Lemma 6.2.
--
--   **Formalization Note** The explicit formula (44) for every $y$, not Mathlib's `ProbabilityTheory.posterior` (which is determined only almost everywhere). For a probability measure $\mu$ the normaliser is positive and $\mu_{t,y}$ is a probability measure.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 6, p.29 (PDF 29), display (44)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- The **posterior** `μ_{t,y} = L(X | Y_t = y)` of the Gaussian additive model with prior `μ`,
given by Bayes' formula (44):
`μ_{t,y}(dx) = e^{−‖y − √t x‖²/2} μ(dx) / ∫ e^{−‖y − √t x′‖²/2} μ(dx′)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 6, p.29 (PDF 29), display (44).

**Formalization Note** The explicit formula (44) for **every** `y`, not Mathlib's
`ProbabilityTheory.posterior`, which is determined only up to a null set of `y`. The normaliser is
positive for every probability measure `μ`, so `posterior μ t y` is a probability measure. -/
noncomputable def posterior {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2) /
    ∫ x', Real.exp (-‖y - Real.sqrt t • x'‖ ^ 2 / 2) ∂μ))

end PhiSobBayes


