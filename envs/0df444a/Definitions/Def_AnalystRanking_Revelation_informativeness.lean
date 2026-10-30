-- Prove2me | Definitions.Def_AnalystRanking_Revelation_informativeness
-- name    : AnalystRanking_Revelation_informativeness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:14.722811+00:00
-- url     : https://prove2.me/theorems/cda69cef-290c-405c-b5cb-bb70cb950922
-- title:
--   Forecast informativeness $\Pi$, Definition 3, (6)
-- statement:
--   The **forecast informativeness** of a symmetric strategy $\sigma$ is the posterior precision of the state given both forecasts, normalized by the prior precision:
--   $$\Pi=\frac{\mathrm{Var}(\omega)}{\mathbb E_{m_i,m_j}[\mathrm{Var}(\omega\mid m_i,m_j)]}-1,\qquad \mathrm{Var}(\omega)=q(1-q),$$
--   with $H=1$ and $L=0$ (Definition 3, (6), p. 24). It is zero when the forecasts carry no information and grows as they reveal more.
--
--   **Formalization Note** The denominator is positive under the standing assumptions, so the division is genuine.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 3, display (6), p. 24

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_expPostVar

namespace AnalystRanking.Revelation

/-- **Forecast informativeness `Π`, Definition 3, (6).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 3, display (6), p. 24:
`Π ≡ Var(ω) / 𝔼_{m_i, m_j}[Var(ω | m_i, m_j)] − 1`, with `H = 1`, `L = 0` and
`Var(ω) = q(1 − q)`.

`informativeness q γ ρ σ` is `Π` of the symmetric strategy `σ`.

**Formalization Note.** `H = 1`, `L = 0` as on p. 24. The denominator `expPostVar` is positive
under the standing hypotheses, so the division is not a junk value. -/
noncomputable def informativeness (q γ ρ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  q * (1 - q) / expPostVar q γ ρ σ - 1

end AnalystRanking.Revelation


