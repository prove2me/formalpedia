-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_noise
-- name    : StochLinOpt_ConfBall2_noise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:50:36.300192+00:00
-- url     : https://prove2.me/theorems/ba04aea4-6a76-426e-9df8-a3095acf6105
-- title:
--   Noise $\eta_t$
-- statement:
--   Along a run, the **noise** of round $t$ is
--
--   $$\eta_t=\ell_t-\mu^\top x_t ,$$
--
--   the difference between the observed loss and its conditional mean.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §2, p. 3; §5.2, p. 8

import Mathlib
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The noise `η_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §2, p. 3: "ηt = ct(xt) − µ · xt"; §5.2, p. 8:
"ηt := ct(xt) − µ†xt = ℓt − E (ℓt | Ht)").

`noise μ x ℓ t = ℓ_t − μ ⬝ x_t`, computed along one path.

**Formalization Note** Pathwise: `x` and `ℓ` are the decisions and losses of one run. -/
def noise {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ℓ t - μ ⬝ᵥ x t

end StochLinOpt.ConfBall2


