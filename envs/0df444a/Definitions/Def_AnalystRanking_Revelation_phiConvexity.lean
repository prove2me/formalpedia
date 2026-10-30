-- Prove2me | Definitions.Def_AnalystRanking_Revelation_phiConvexity
-- name    : AnalystRanking_Revelation_phiConvexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:31:48.700493+00:00
-- url     : https://prove2.me/theorems/79160b8e-c34a-4bfc-8508-2c51a4e0a4b5
-- title:
--   Payoff convexity $\varphi=W_1/W_2$, (4)
-- statement:
--   With $W_1=w_1-w_0>0$ (gain from a high rank versus a tie) and $W_2=w_0-w_2>0$ (loss from a low rank versus a tie), payoff convexity is
--   $$\varphi=\frac{W_1}{W_2}=\frac{w_1-w_0}{w_0-w_2}>0 .$$
--   The payoff structure is convex if $\varphi>1$, concave if $\varphi<1$ and linear if $\varphi=1$ ((4), p. 8).
--
--   **Formalization Note** Statements assume $w_2<w_0<w_1$, so the denominator is positive.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, display (4), p. 8

import Mathlib

namespace AnalystRanking.Revelation

/-- **Payoff convexity `φ = W₁/W₂`, (4).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, display (4), p. 8: `W₁ ≡ w₁ − w₀ > 0`, `W₂ ≡ w₀ − w₂ > 0` and `φ ≡ W₁/W₂ > 0`; the payoff
structure is convex if `φ > 1`, concave if `φ < 1`, linear if `φ = 1`.

**Formalization Note.** Statements using `phiConvexity` assume `w₂ < w₀ < w₁`, so the
denominator is positive. -/
noncomputable def phiConvexity (w1 w0 w2 : ℝ) : ℝ :=
  (w1 - w0) / (w0 - w2)

end AnalystRanking.Revelation


