-- Prove2me | Definitions.Def_AnalystRanking_Revelation_rhoBar
-- name    : AnalystRanking_Revelation_rhoBar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:41:46.975755+00:00
-- url     : https://prove2.me/theorems/5377a1d4-37fd-4b13-843f-70a578d94d37
-- title:
--   Correlation threshold $\bar\rho$, (B.3)
-- statement:
--   $$\bar\rho=1-\frac{1}{2\gamma}$$ ((B.3), p. 34). For $\gamma\in(\tfrac12,1)$, $\bar\rho\in(0,\tfrac12)$; it separates low from high signal correlation in Claim 1 (B.2) and Proposition 3.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.2), (B.3), p. 34

import Mathlib

namespace AnalystRanking.Revelation

/-- **The correlation threshold `ρ̄`, (B.3).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.2), display (B.3), p. 34: `ρ̄ ≡ 1 − 1/(2γ)`. -/
noncomputable def rhoBar (γ : ℝ) : ℝ :=
  1 - 1 / (2 * γ)

end AnalystRanking.Revelation


