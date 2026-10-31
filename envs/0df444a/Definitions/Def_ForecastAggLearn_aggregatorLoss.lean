-- Prove2me | Definitions.Def_ForecastAggLearn_aggregatorLoss
-- name    : ForecastAggLearn_aggregatorLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:10.877706+00:00
-- url     : https://prove2.me/theorems/c2f5699f-6002-4313-98e0-1dc093bc2e06
-- title:
--   Total expected log loss of an aggregator
-- statement:
--   Fix an aggregator, an evidence matrix $A$ (through the sets $A_i$), and sequences of priors $\mu_t$ and conditional laws $C_{t,j}^\omega$. In period $t$ expert $i$ reports $F_{i,t}=\mathbb P(\omega_t=1\mid (s_{t,j})_{j\in A_i})$, computed under period $t$'s information structure, and the aggregator forecasts $r_t$ from $(\mu_{t'})_{t'\le t}$, $(F_{t'})_{t'\le t}$ and $(\omega_{t'})_{t'<t}$. The aggregator's total expected loss is
--
--   $$
--   \mathbb E\Bigl[\sum_{t=1}^T l(r_t,\omega_t)\Bigr],
--   $$
--
--   the expectation over the $T$ independent periods. Subtracting the benchmark's total gives the regret of Definition 1.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral of a $[0,\infty]$-valued function, so an infinite loss is never truncated.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, Definition 1, p.10

import Mathlib
import Definitions.Def_ForecastAggLearn_post
import Definitions.Def_ForecastAggLearn_logLoss
import Definitions.Def_ForecastAggLearn_dynamicLaw
import Definitions.Def_ForecastAggLearn_PriorAwareAggregator

namespace ForecastAggLearn

open MeasureTheory

/-- **Total expected logarithmic loss of a prior-aware aggregator.**
Babichenko, Garber, arXiv:1802.07107v1, Definition 1, p.10: the aggregator's part
`Σ_{t∈[T]} E_{s_t∼C_t, ω_t∼C_t|s_t} l(r_t, ω_t)` of the total regret.

In period `t`, expert `i` reports `F_{i,t} = post (μ t) (P t) (A_i) s_t` (eq. (2), p.9), and the
aggregator forecasts `r_t = alg.forecast t (μ_0..μ_t) (F_0..F_t) (ω_0..ω_{t−1})`.

**Formalization Note.** The expectation is the lower Lebesgue integral `∫⁻` of the
`ℝ≥0∞`-valued total loss over the product law `dynamicLaw` of the `T` independent periods, so an
infinite loss is never truncated. Periods are 0-based. -/
noncomputable def aggregatorLoss {n m T : ℕ} (alg : PriorAwareAggregator n T)
    (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j)) : ENNReal :=
  ∫⁻ x, ∑ t : Fin T,
      logLoss
        (alg.forecast t (fun u => μ u.val)
          (fun u i => post (μ u.val) (P u.val) (Aset i) (x ⟨u.val, by omega⟩).2)
          (fun u => (x ⟨u.val, by omega⟩).1))
        (x t).1
    ∂(dynamicLaw T μ P)

end ForecastAggLearn


