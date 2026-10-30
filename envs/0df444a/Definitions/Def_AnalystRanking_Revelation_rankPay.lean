-- Prove2me | Definitions.Def_AnalystRanking_Revelation_rankPay
-- name    : AnalystRanking_Revelation_rankPay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:31:34.579638+00:00
-- url     : https://prove2.me/theorems/52032ad6-21d5-4703-91e8-581a0a6e3ba3
-- title:
--   Rank payoff $u_i(r_i(m_i,m_j,\omega))$, (3)
-- statement:
--   After the state is revealed, analyst $i$ is ranked high ($r_h$) if his forecast is correct and the other's is not, low ($r_l$) in the opposite case, and the two tie ($r_t$) when they forecast the same thing. His payoff is
--   $$u_i=\begin{cases}w_1,& r_i=r_h,\\ w_0,& r_i=r_t,\\ w_2,& r_i=r_l,\end{cases}\qquad w_1>w_0>w_2$$
--   ((3), p. 8). With binary forecasts, different forecasts mean exactly one of them is correct.
--
--   **Formalization Note** The payoff is a function of the own forecast $m$, the other's forecast $m_j$ and the state $\omega$, all `Bool`.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, display (3) and the ranking rule, p. 8

import Mathlib

namespace AnalystRanking.Revelation

/-- **Rank payoff, (3).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 8: "`r_i(m_i, m_j, ω) = r_h` if `m_i = ω ≠ m_j`, and `r_i(m_i, m_j, ω) = r_l` if
`m_i ≠ ω = m_j`. If both analysts make the same forecast, then they tie; i.e.,
`r_i(m_i, m_j, ω) = r_t` if `m_i = m_j`", and (3): the payoff is `w₁` at `r_h`, `w₀` at `r_t`,
`w₂` at `r_l`, with `w₁ > w₀ > w₂`.

`rankPay w1 w0 w2 m mj ω` is analyst `i`'s payoff when he forecasts `m`, the other analyst
forecasts `mj` and the state is `ω`.

**Formalization Note.** Forecasts and states are `Bool` (`true = ĥ`, `true = H`). With binary
forecasts, `m ≠ mj` means exactly one of them equals `ω`, so the three cases are exhaustive. -/
noncomputable def rankPay (w1 w0 w2 : ℝ) (m mj ω : Bool) : ℝ :=
  if m = mj then w0 else if m = ω then w1 else w2

end AnalystRanking.Revelation


