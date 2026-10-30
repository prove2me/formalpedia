-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_width
-- name    : StochLinOpt_ConfBall2_width
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:49:22.202824+00:00
-- url     : https://prove2.me/theorems/c59c1a91-198a-4851-b9fc-240893402dde
-- title:
--   Normalized width $w_t$
-- statement:
--   The **normalized width** at round $t$ is
--
--   $$w_t=\sqrt{x_t^\top A_t^{-1}x_t},$$
--
--   the size of the confidence ellipsoid in the direction of the chosen decision; $2\sqrt{\beta_t}\,w_t$ bounds the instantaneous regret.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §5.1, p. 7 (definition of w_t)

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_gram
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The normalized width `w_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §5.1, p. 7: "Define wt := √(x†tA−1t xt)").

`width b x t = √(x_tᵀ A_t⁻¹ x_t)`.

**Formalization Note** `Real.sqrt` and Mathlib's matrix inverse are total; under the spanner and
full-rank hypotheses of every statement, `A_t` is positive definite and the radicand is `≥ 0`. -/
noncomputable def width {n : ℕ} (b : Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  Real.sqrt (x t ⬝ᵥ ((gram b x t)⁻¹ *ᵥ x t))

end StochLinOpt.ConfBall2


