-- Prove2me | Definitions.Def_AnalystRanking_Revelation_phiBar
-- name    : AnalystRanking_Revelation_phiBar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:05.377493+00:00
-- url     : https://prove2.me/theorems/50fb1e35-3a5b-435f-89aa-116ea4c7d8c1
-- title:
--   Convexity threshold $\bar\varphi$, (B.4)
-- statement:
--   With $\chi=\rho\gamma(1-\gamma)$,
--   $$\bar\varphi=\frac{\chi+\gamma(\gamma-\tfrac12)}{\chi-(1-\gamma)(\gamma-\tfrac12)}$$
--   ((B.4), p. 34). Its denominator is positive exactly when $\rho>\bar\rho$, the only case in which the paper uses it; then $\bar\varphi>1$, and $\check q_{\min}\le\tfrac12$ iff $\varphi\ge\bar\varphi$.
--
--   **Formalization Note** Every statement using $\bar\varphi$ assumes $\rho>\bar\rho$.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.2), (B.4), p. 34

import Mathlib

namespace AnalystRanking.Revelation

/-- **The convexity threshold `φ̄`, (B.4).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.2), display (B.4), p. 34:
`φ̄ ≡ (χ + γ(γ − 1/2)) / (χ − (1 − γ)(γ − 1/2))`, with `χ = ργ(1 − γ)`.

**Formalization Note.** The denominator is positive exactly when `ρ > ρ̄`; the paper uses `φ̄` only
there, and every statement using `phiBar` assumes `rhoBar γ < ρ` (otherwise Lean's `x / 0 = 0`
or a negative value would be meaningless). -/
noncomputable def phiBar (γ ρ : ℝ) : ℝ :=
  let χ := ρ * γ * (1 - γ)
  (χ + γ * (γ - 1 / 2)) / (χ - (1 - γ) * (γ - 1 / 2))

end AnalystRanking.Revelation


