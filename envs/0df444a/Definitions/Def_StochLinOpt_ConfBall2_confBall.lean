-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_confBall
-- name    : StochLinOpt_ConfBall2_confBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:48:07.866882+00:00
-- url     : https://prove2.me/theorems/7a6fcd40-6abd-42f2-b392-1f6508431cd7
-- title:
--   Confidence ellipsoid $B^2_t$
-- statement:
--   The **confidence ellipsoid** of ConfidenceBall$_2$ at round $t$ is
--
--   $$B^2_t=\bigl\{\nu\in\mathbb R^n:\ \|\nu-\widehat\mu_t\|_{2,A_t}\le\sqrt{\beta_t}\bigr\}
--   =\bigl\{\nu:\ (\nu-\widehat\mu_t)^\top A_t(\nu-\widehat\mu_t)\le\beta_t\bigr\},$$
--
--   where $\|v\|_{2,A}=\sqrt{v^\top Av}$. It depends only on the decisions and losses of rounds $1,\dots,t-1$.
--
--   **Formalization Note** The ball is written with the quadratic form, which is equivalent because $\beta_t\ge0$; no matrix square root is used.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Algorithm 3.1, p. 4; §2, p. 3 (A-norms)

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_gram
import Definitions.Def_StochLinOpt_ConfBall2_lsEst
import Definitions.Def_StochLinOpt_ConfBall2_beta
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The confidence ellipsoid `B²_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Algorithm 3.1, p. 4:
"B2t = {ν: ‖ν − µ̂t‖_{2,At} ≤ √βt}"; §2, p. 3: "‖ν‖_{2,A} := ‖A^{1/2}ν‖2 = √(ν†Aν)").

`confBall b x ℓ δ t = {ν | (ν − µ̂_t)ᵀ A_t (ν − µ̂_t) ≤ β_t}`.

**Formalization Note** The ball is written with the quadratic form: `√(vᵀAv) ≤ √β ⟺ vᵀAv ≤ β`
because `β_t ≥ 0`, so no matrix square root is needed. -/
noncomputable def confBall {n : ℕ} (b : Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (δ : ℝ) (t : ℕ) : Set (Fin n → ℝ) :=
  {ν | (ν - lsEst b x ℓ t) ⬝ᵥ (gram b x t *ᵥ (ν - lsEst b x ℓ t)) ≤ beta n δ t}

end StochLinOpt.ConfBall2


