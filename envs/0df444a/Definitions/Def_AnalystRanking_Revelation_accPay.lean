-- Prove2me | Definitions.Def_AnalystRanking_Revelation_accPay
-- name    : AnalystRanking_Revelation_accPay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:32:06.564166+00:00
-- url     : https://prove2.me/theorems/212f8da7-16c1-4cf7-98ae-0ba9a353e9c7
-- title:
--   Benchmark accuracy payoff, $\pi_a=W$, $\pi_{na}=0$
-- statement:
--   In the benchmark without ranking (§3.1, p. 10), an analyst is paid only for his own accuracy:
--   $$u_i(m,\omega)=\begin{cases}W,& m=\omega,\\ 0,& m\neq\omega,\end{cases}$$
--   the paper's normalization $\pi_a=W$, $\pi_{na}=0$.
--
--   **Formalization Note** Statements assume $W>0$.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §3.1, p. 10

import Mathlib

namespace AnalystRanking.Revelation

/-- **Benchmark accuracy payoff.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §3.1, p. 10: "`u_i(m_i, ω) = π_a` if `m_i = ω`, and `u_i(m_i, ω) = π_na` if `m_i ≠ ω` …
Without loss of generality, assume that `π_a = W` and `π_na = 0`."

**Formalization Note.** Forecasts and states are `Bool` (`true = ĥ`, `true = H`). Statements
assume `0 < W`. -/
noncomputable def accPay (W : ℝ) (m ω : Bool) : ℝ :=
  if m = ω then W else 0

end AnalystRanking.Revelation


