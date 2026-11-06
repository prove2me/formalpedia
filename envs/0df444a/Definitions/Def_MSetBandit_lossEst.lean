-- Prove2me | Definitions.Def_MSetBandit_lossEst
-- name    : MSetBandit_lossEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:55.578094+00:00
-- url     : https://prove2.me/theorems/45f6eeb5-9f5b-4f1c-98ac-227f481d967e
-- title:
--   Loss estimate $\hat\ell=M^{-1}XY$
-- statement:
--   Let $\theta\in\mathbb R^d$, $p=p_\theta$, $M=M(p)$. For a drawn action $X_0\in\mathcal X$ and an observed loss $Y\in\mathbb R$, the **loss estimate** is
--   $$
--   \hat\ell=M^{-1}X_0\,Y\in\mathbb R^d .
--   $$
--   In Algorithm 1 (line 9), $\hat\ell_t=M_t^{-1}X_tY_t$ with $X_t\sim p_t$ and $Y_t=X_t^\top\ell_t$.
--
--   **Formalization Note** $M^{-1}$ is the matrix inverse; $M(p_\theta)$ is positive definite whenever $1\le m\le d-1$ (Lemma 2), so it is the true inverse in every use.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Eq. (6), p.5; Algorithm 1, line 9, p.12

import Mathlib
import Definitions.Def_MSetBandit_secondMoment
import Definitions.Def_MSetBandit_wdist
open Matrix

namespace MSetBandit

/-- **The loss estimate `ℓ̂_t = M_t⁻¹ X_t Y_t`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Eq. (6), p.5, and Algorithm 1, line 9,
p.12: after drawing the action `X_t` from `p_t = p_{θ_t}` and observing `Y_t = X_t^⊤ ℓ_t`, the
learner computes `ℓ̂_t ← M_t⁻¹ X_t Y_t` with `M_t = M(p_t)`.

`lossEst θ X₀ Y` is `M(p_θ)⁻¹ 1_{X₀} Y`.

**Formalization Note.** `M⁻¹` is Mathlib's matrix inverse (`0` for a singular matrix); for a
weighted m-set distribution with `1 ≤ m ≤ d − 1` the matrix `M(p_θ)` is positive definite
(Lemma 2), so the inverse is the true one. -/
noncomputable def lossEst {d m : ℕ} (θ : Fin d → ℝ) (X₀ : Action d m) (Y : ℝ) : Fin d → ℝ :=
  Y • ((secondMoment (wdist (m := m) θ))⁻¹ *ᵥ ind X₀)

end MSetBandit


