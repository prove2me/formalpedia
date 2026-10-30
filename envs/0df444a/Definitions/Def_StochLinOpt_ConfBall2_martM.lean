-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_martM
-- name    : StochLinOpt_ConfBall2_martM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:52:54.291997+00:00
-- url     : https://prove2.me/theorems/3c50b409-d413-49f2-9558-e68b43b8db32
-- title:
--   Martingale increment $M_t$
-- statement:
--   Along a run, the **martingale increment** of round $t$ is
--
--   $$M_t=2\,\eta_t\,E_t\,\frac{x_t^\top(\widehat\mu_t-\mu)}{1+w_t^2}.$$
--
--   Lemma 13 shows that $(M_t)$ is a martingale difference sequence with respect to the histories $\mathcal H_t$.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Lemma 13, p. 9

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_noise
import Definitions.Def_StochLinOpt_ConfBall2_escape
import Definitions.Def_StochLinOpt_ConfBall2_lsEst
import Definitions.Def_StochLinOpt_ConfBall2_width
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The martingale increment `M_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Lemma 13, p. 9: "Define a random variable Mt by
Mt = 2ηtEt x†t(µ̂t − µ)/(1 + w2t)").

`martM b x ℓ μ δ t = 2 η_t E_t x_tᵀ(µ̂_t − μ) / (1 + w_t²)`.

**Formalization Note** Pathwise: evaluated on the decisions and losses of one run. -/
noncomputable def martM {n : ℕ} (b : Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (μ : Fin n → ℝ) (δ : ℝ) (t : ℕ) : ℝ :=
  2 * noise μ x ℓ t * escape b x ℓ μ δ t * (x t ⬝ᵥ (lsEst b x ℓ t - μ)) /
    (1 + width b x t ^ 2)

end StochLinOpt.ConfBall2


