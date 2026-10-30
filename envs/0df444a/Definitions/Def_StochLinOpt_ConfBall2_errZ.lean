-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_errZ
-- name    : StochLinOpt_ConfBall2_errZ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:51:12.046981+00:00
-- url     : https://prove2.me/theorems/0abbc1ed-51eb-4d9e-a387-0b52c40dbe9d
-- title:
--   Estimation error $Z_t$
-- statement:
--   Along a run, the **estimation error** at round $t$ is
--
--   $$Z_t=(\widehat\mu_t-\mu)^\top A_t(\widehat\mu_t-\mu).$$
--
--   $Z_t\le\beta_t$ is exactly the event $\mu\in B^2_t$. At $t=1$, $Z_1=\mu^\top A_1\mu$.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §5.2, p. 8

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_gram
import Definitions.Def_StochLinOpt_ConfBall2_lsEst
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The estimation error `Z_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §5.2, p. 8: "Zt := (µ̂t − µ)†At(µ̂t − µ)").

`errZ b x ℓ μ t = (µ̂_t − μ)ᵀ A_t (µ̂_t − μ)`.

**Formalization Note** Pathwise; rounds are 1-based, so `errZ b x ℓ μ 1 = μᵀ A_1 μ`. -/
noncomputable def errZ {n : ℕ} (b : Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (μ : Fin n → ℝ) (t : ℕ) : ℝ :=
  (lsEst b x ℓ t - μ) ⬝ᵥ (gram b x t *ᵥ (lsEst b x ℓ t - μ))

end StochLinOpt.ConfBall2


