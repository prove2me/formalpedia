-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_beta
-- name    : StochLinOpt_ConfBall2_beta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:46:51.898723+00:00
-- url     : https://prove2.me/theorems/6239a2ae-5692-4f64-ae02-c67f281a8b72
-- title:
--   Confidence radius $\beta_t$
-- statement:
--   For a dimension $n$, a confidence parameter $\delta$ and a round $t\ge 1$, the **confidence radius** of ConfidenceBall$_2$ is
--
--   $$\beta_t=\max\Bigl(128\,n\ln t\,\ln(t^2/\delta),\ \bigl(\tfrac83\ln(t^2/\delta)\bigr)^2\Bigr),$$
--
--   with natural logarithms. It is nondecreasing in $t$ for $0<\delta<1$, and at $t=1$ it equals $\bigl(\tfrac83\ln(1/\delta)\bigr)^2$ because $\ln 1=0$.
--
--   **Formalization Note** The value is a real number for every $\delta$; it is nonnegative because the second term is a square.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Algorithm 3.1, p. 4; Theorem 2, p. 5

import Mathlib
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The confidence radius `β_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Algorithm 3.1, p. 4, and Theorem 2, p. 5:
"βt = max(128n ln t ln(t²/δ), ((8/3) ln(t²/δ))²)").

`beta n δ t = max (128 n ln t ln(t²/δ)) (((8/3) ln(t²/δ))²)`, with natural logarithms.

**Formalization Note** Rounds are 1-based: only `t ≥ 1` is used, and `β_1 = ((8/3) ln(1/δ))²`
because `ln 1 = 0`. For `0 < δ < 1` (the paper's range) all logarithms have positive arguments;
the value is a nonnegative real for every `δ`, since the second term is a square. -/
noncomputable def beta (n : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  max (128 * (n : ℝ) * Real.log t * Real.log ((t : ℝ) ^ 2 / δ))
    ((8 / 3 * Real.log ((t : ℝ) ^ 2 / δ)) ^ 2)

end StochLinOpt.ConfBall2


