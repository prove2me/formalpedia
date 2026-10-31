-- Prove2me | Definitions.Def_ForecastAggLearn_PriorAwareAggregator
-- name    : ForecastAggLearn_PriorAwareAggregator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:16.406085+00:00
-- url     : https://prove2.me/theorems/d2abf5f1-a911-492c-b13e-d3e7bf3a46e3
-- title:
--   Prior-aware aggregator over $T$ periods
-- statement:
--   A **prior-aware aggregator** for $n$ experts over $T$ periods is a rule that, in each period $t$, forecasts
--
--   $$
--   r_t=r_t\bigl(\mu_1,\dots,\mu_t;\ F_1,\dots,F_t;\ \omega_1,\dots,\omega_{t-1}\bigr)\in[0,1],
--   $$
--
--   from the priors so far (it "shares the common prior with the experts"), the forecast profiles $F_{t'}\in\mathbb R^n$ of the current and past periods, and the past states. It sees nothing else: not the signals, not the number of signals, not the evidence matrix, not the signal laws, and not $\omega_t$.
--
--   The paper's two environments differ in what this rule may use; this is the information constraint of Theorem 2.
--
--   **Formalization Note** The information constraint is enforced by the type of `forecast`. The rule is deterministic, jointly measurable and $[0,1]$-valued, as the paper's algorithm is. Periods are 0-based.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, p.10; §1, p.2; §4.2, p.16

import Mathlib

namespace ForecastAggLearn

/-- **A prior-aware aggregator for `n` experts over `T` periods.**
Babichenko, Garber, arXiv:1802.07107v1, p.10: "on each period t, the aggregator observes the
current profile of forecasts F_t and the history of the past forecasts and realizations
(F_{t'}, ω_{t'})_{t'<t}. The aggregator provides a forecast r_t (before the actual state is
realized)"; p.2: a prior-aware aggregator is "one that shares the common prior with the experts";
p.16: "on each round t he knows the sequence (µ_i)_{i≤t}"; p.9: his forecast is `r ∈ [0, 1]`.

`forecast t μs Fs ωs` is the forecast `r_t` given the priors `μ_0, …, μ_t`, the forecast profiles
`F_0, …, F_t ∈ ℝⁿ` and the past states `ω_0, …, ω_{t−1}`.

**Formalization Note.** The type is the information constraint: the forecast cannot depend on
`ω_t`, on later periods, on the signals, on the number of signals `m`, on the evidence matrix or
on the signal laws. Periods are 0-based. The rule is deterministic, jointly measurable and
`[0, 1]`-valued; the paper's algorithm is of this kind. -/
structure PriorAwareAggregator (n T : ℕ) where
  /-- The forecast `r_t` from the priors, the forecast profiles up to `t`, and past states. -/
  forecast : (t : Fin T) → (Fin (t.val + 1) → ℝ) → (Fin (t.val + 1) → Fin n → ℝ) →
    (Fin t.val → Bool) → ℝ
  /-- Each forecast rule is jointly measurable. -/
  measurable_forecast : ∀ t : Fin T,
    Measurable (fun p : (Fin (t.val + 1) → ℝ) × (Fin (t.val + 1) → Fin n → ℝ) × (Fin t.val → Bool) =>
      forecast t p.1 p.2.1 p.2.2)
  /-- Forecasts are probabilities. -/
  forecast_mem_Icc : ∀ t μs Fs ωs, forecast t μs Fs ωs ∈ Set.Icc (0 : ℝ) 1

end ForecastAggLearn


