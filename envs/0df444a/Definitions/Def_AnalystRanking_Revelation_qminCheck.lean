-- Prove2me | Definitions.Def_AnalystRanking_Revelation_qminCheck
-- name    : AnalystRanking_Revelation_qminCheck
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:28.656864+00:00
-- url     : https://prove2.me/theorems/d52f76b1-9b9c-4218-a8f6-971e56ef7f68
-- title:
--   The threshold $q_{\min}$, (B.2)
-- statement:
--   For $\gamma,\rho,\varphi$ let $\chi=\rho\gamma(1-\gamma)$ and
--   $$q_{\min}=\gamma-\chi\left[\frac{\varphi-1}{(1-\gamma)\varphi+\gamma}\right]$$
--   ((B.2), p. 34). For convex payoffs ($\varphi>1$) it is the paper's $\check q_{\min}<\gamma$, for concave payoffs $\hat q_{\min}>\gamma$ ((B.1), p. 33). Under competition, separation $(1,1)$ is a best reply to itself exactly on $[1-q_{\min},q_{\min}]$ (Claim 1).
--
--   **Formalization Note** At $\rho=0$ the value is $\gamma$.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.1), display (B.2), p. 34; (B.1), p. 33

import Mathlib

namespace AnalystRanking.Revelation

/-- **The threshold `q_min`, (B.2).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.1), display (B.2), p. 34 (and (B.29), p. 45, (B.42), p. 50):
`q_min = γ − χ[(φ − 1)/((1 − γ)φ + γ)]` with `χ = ργ(1 − γ)`; `q̌_min ≡ q_min(φ > 1)` and
`q̂_min ≡ q_min(φ < 1)` ((B.1), p. 33).

**Formalization Note.** For `1/2 < γ < 1` and `φ > 0` the denominator `(1 − γ)φ + γ` is positive.
At `ρ = 0` the value is `γ`. -/
noncomputable def qminCheck (γ ρ φ : ℝ) : ℝ :=
  γ - ρ * γ * (1 - γ) * ((φ - 1) / ((1 - γ) * φ + γ))

end AnalystRanking.Revelation


