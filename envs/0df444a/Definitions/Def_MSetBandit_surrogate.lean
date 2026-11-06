-- Prove2me | Definitions.Def_MSetBandit_surrogate
-- name    : MSetBandit_surrogate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:00.593205+00:00
-- url     : https://prove2.me/theorems/2fc5fe65-e992-40e6-9d91-4230688cd2c0
-- title:
--   Surrogate loss $Z(x)=x^\top\hat\ell-\eta c_p^\top x$
-- statement:
--   Let $\eta\in\mathbb R$, $\theta\in\mathbb R^d$, $p=p_\theta$, and let $\hat\ell=M(p)^{-1}X_0Y$ be the loss estimate built from a drawn action $X_0$ and an observed loss $Y$. The **surrogate loss** of an action $x$ is
--   $$
--   Z(x)=\hat y(x)-\eta\,c_p^\top x,\qquad \hat y(x)=x^\top\hat\ell .
--   $$
--   In Algorithm 1 this is $Z_t(x)=\hat y_t(x)-\eta c_t^\top x$ with $c_t=c_{p_t}$; it is linear in $x$, $Z_t(x)=z_t^\top x$ with $z_t=\hat\ell_t-\eta c_t$.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 5.2, p.11; Appendix C, p.26

import Mathlib
import Definitions.Def_MSetBandit_lossEst
import Definitions.Def_MSetBandit_cvec
open Matrix

namespace MSetBandit

/-- **The surrogate loss `Z_t(x) = ŷ_t(x) − η c_t^⊤ x`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 5.2, p.11, and
Appendix C, p.26: `Z_t(x) := ŷ_t(x) − η c_t^⊤ x` with `ŷ_t(x) = x^⊤ ℓ̂_t`, `c_t = c_{p_t}`,
`p_t = p_{θ_t}`.

`surrogate η θ X₀ Y x` is `x^⊤ ℓ̂ − η c_{p_θ}^⊤ x`, where `ℓ̂ = lossEst θ X₀ Y` is built from the
drawn action `X₀` and the observed loss `Y`. -/
noncomputable def surrogate {d m : ℕ} (η : ℝ) (θ : Fin d → ℝ) (X₀ : Action d m) (Y : ℝ)
    (x : Action d m) : ℝ :=
  ind x ⬝ᵥ lossEst θ X₀ Y - η * (cvec (wdist (m := m) θ) ⬝ᵥ ind x)

end MSetBandit


