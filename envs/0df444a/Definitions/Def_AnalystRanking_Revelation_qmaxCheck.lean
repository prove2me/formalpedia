-- Prove2me | Definitions.Def_AnalystRanking_Revelation_qmaxCheck
-- name    : AnalystRanking_Revelation_qmaxCheck
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:19.895776+00:00
-- url     : https://prove2.me/theorems/67838124-1b37-4de5-b4a5-e5a10191fdc5
-- title:
--   The threshold $\check q_{\max}$, (B.22)
-- statement:
--   $$\check q_{\max}=\frac{\varphi\gamma}{1-\gamma+\varphi\gamma}\in(\gamma,1)\quad(\varphi>1)$$ ((B.22), p. 42). Above it the only equilibrium under convex payoffs is pooling.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), proof of Proposition 2, (B.22), p. 42; (B.1), p. 33

import Mathlib

namespace AnalystRanking.Revelation

/-- **The threshold `q̌_max`, (B.22).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), proof of Proposition 2, display (B.22), p. 42: `q̌_max = φγ/(1 − γ + φγ) ∈ (γ, 1)`
(defined in (B.1), p. 33, by `ΔUˡ_i(1, 0, q̌_max) = 0`). -/
noncomputable def qmaxCheck (γ φ : ℝ) : ℝ :=
  φ * γ / (1 - γ + φ * γ)

end AnalystRanking.Revelation


