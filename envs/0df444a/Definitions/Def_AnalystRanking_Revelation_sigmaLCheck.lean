-- Prove2me | Definitions.Def_AnalystRanking_Revelation_sigmaLCheck
-- name    : AnalystRanking_Revelation_sigmaLCheck
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:35.157583+00:00
-- url     : https://prove2.me/theorems/6db51996-6f9c-45e2-83ec-1d035f80272e
-- title:
--   Semi-separating strategy $\check\sigma^l(q)$, (B.30)
-- statement:
--   With $\chi=\rho\gamma(1-\gamma)$,
--   $$\check\sigma^l(q)=1-\frac{\big[\tfrac{(1-\gamma)\varphi+\gamma}{\varphi-1}\big](q-\gamma)+\chi}{\big[q(1-\gamma)^2+(1-q)\gamma^2\big]+\chi}$$
--   ((B.30), p. 45). It solves $\Delta U^l_i(1,\sigma^l,q)=0$; by symmetry $\check\sigma^h(q)=\check\sigma^l(1-q)$ ((B.42), p. 50).
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), proof of Proposition 3, (B.30), p. 45; (B.42), p. 50

import Mathlib

namespace AnalystRanking.Revelation

/-- **The semi-separating strategy `σ̌ˡ(q)`, (B.30).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), proof of Proposition 3, display (B.30), p. 45 (also (B.42), p. 50):
`σ̌ˡ(q) = 1 − ([((1 − γ)φ + γ)/(φ − 1)](q − γ) + χ) / ([q(1 − γ)² + (1 − q)γ²] + χ)`,
with `χ = ργ(1 − γ)`; by (B.42) `σ̌ʰ(q) = σ̌ˡ(1 − q)`.

**Formalization Note.** Transcribed as printed; statements use it with `φ > 1`. -/
noncomputable def sigmaLCheck (γ ρ φ q : ℝ) : ℝ :=
  let χ := ρ * γ * (1 - γ)
  1 - (((1 - γ) * φ + γ) / (φ - 1) * (q - γ) + χ) / ((q * (1 - γ) ^ 2 + (1 - q) * γ ^ 2) + χ)

end AnalystRanking.Revelation


