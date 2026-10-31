-- Prove2me | Definitions.Def_ForecastAggLearn_logLoss
-- name    : ForecastAggLearn_logLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:17.415358+00:00
-- url     : https://prove2.me/theorems/56b0371b-4873-4e99-aec5-b83772921153
-- title:
--   Logarithmic loss $l(r,\omega)$
-- statement:
--   The aggregator's forecast $r\in[0,1]$ is scored by the **logarithmic loss**
--
--   $$
--   l(r,\omega)=\begin{cases}-\ln r & \omega=1,\\ -\ln(1-r) & \omega=0,\end{cases}
--   $$
--
--   with values in $[0,\infty]$: a forecast $r=0$ when $\omega=1$, or $r=1$ when $\omega=0$, costs $+\infty$.
--
--   This is the loss in which regret is measured throughout the paper.
--
--   **Formalization Note** $\omega$ is `Bool` (`true` is $\omega=1$). The loss is $[0,\infty]$-valued (`ℝ≥0∞`): $r\le0$ with $\omega=1$ and $r\ge1$ with $\omega=0$ give $\infty$, so a confident wrong forecast is never free.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, p.10

import Mathlib

namespace ForecastAggLearn

/-- **Logarithmic loss.**
Babichenko, Garber, arXiv:1802.07107v1, §2, p.10: "We measure the aggregator's performance with
respect to the logarithmic loss: l(r, ω) = −ln(r) if ω = 1, −ln(1 − r) if ω = 0."

**Formalization Note.** Ω = {0, 1} is `Bool` (`true` is ω = 1). The loss takes values in
`ℝ≥0∞`: a forecast `r ≤ 0` when ω = 1, or `r ≥ 1` when ω = 0, has loss `⊤ = +∞`, as
`−ln 0 = +∞`. (A real-valued loss would give these confident wrong forecasts loss `0`, because
`Real.log 0 = 0`.) For `r ∈ (0, 1]` (ω = 1) and `r ∈ [0, 1)` (ω = 0) it is the printed value. -/
noncomputable def logLoss (r : ℝ) (ω : Bool) : ENNReal :=
  if ω then (if r ≤ 0 then ⊤ else ENNReal.ofReal (-Real.log r))
  else (if 1 ≤ r then ⊤ else ENNReal.ofReal (-Real.log (1 - r)))

end ForecastAggLearn


