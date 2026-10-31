-- Prove2me | Definitions.Def_ForecastAggLearn_benchmarkLoss
-- name    : ForecastAggLearn_benchmarkLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:29.009968+00:00
-- url     : https://prove2.me/theorems/589812fc-cb4f-476f-8581-039b9311c63a
-- title:
--   Total expected log loss of the Bayes-optimal forecast $r^*$
-- statement:
--   For sequences of priors $\mu_t$ and conditional laws $C_{t,j}^\omega$, the benchmark forecasts in period $t$ the Bayes posterior given all $m$ signals, $r^*(s_t)=\mathbb P(\omega_t=1\mid s_{t,1},\dots,s_{t,m})$. Its total expected loss is
--
--   $$
--   \mathbb E\Bigl[\sum_{t=1}^T l(r^*(s_t),\omega_t)\Bigr].
--   $$
--
--   This is the "most competitive benchmark" of the paper: the optimal forecast that aggregates all the information in the system, not the best expert.
--
--   **Formalization Note** $r^*(s_t)$ is `post (μ t) (P t) Finset.univ`. The expectation is a lower Lebesgue integral of a $[0,\infty]$-valued function.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, Definition 1, p.10; eq. (1), p.9

import Mathlib
import Definitions.Def_ForecastAggLearn_post
import Definitions.Def_ForecastAggLearn_logLoss
import Definitions.Def_ForecastAggLearn_dynamicLaw

namespace ForecastAggLearn

open MeasureTheory

/-- **Total expected logarithmic loss of the Bayes-optimal benchmark.**
Babichenko, Garber, arXiv:1802.07107v1, Definition 1, p.10: the benchmark's part
`Σ_{t∈[T]} E_{s_t∼C_t, ω_t∼C_t|s_t} l(r*(s_t), ω_t)` of the total regret, where
`r*(s) = P(ω = 1 | s_1, …, s_m)` aggregates all `m` signals (eq. (1), p.9).

**Formalization Note.** `r*(s_t) = post (μ t) (P t) Finset.univ s_t`. The expectation is `∫⁻` of
the `ℝ≥0∞`-valued total loss over the product law of the `T` periods (0-based). -/
noncomputable def benchmarkLoss (T : ℕ) {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j)) : ENNReal :=
  ∫⁻ x, ∑ t : Fin T, logLoss (post (μ t) (P t) Finset.univ (x t).2) (x t).1
    ∂(dynamicLaw T μ P)

end ForecastAggLearn


