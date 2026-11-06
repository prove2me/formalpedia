-- Prove2me | Definitions.Def_MSetBandit_mwuParam
-- name    : MSetBandit_mwuParam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:29.841894+00:00
-- url     : https://prove2.me/theorems/6bcd06ad-4d03-47cb-94f5-fc2f8ee1f107
-- title:
--   Multiplicative-weights parameter $\tilde\theta_{t+1}=\theta_t-\eta z_t$
-- statement:
--   Given the current parameter $\theta$, the drawn action $X_0$ and the observed loss $Y$, the unprojected multiplicative-weights step of Algorithm 1 (line 10) produces
--   $$
--   \tilde\theta=\theta-\eta z,\qquad z=\hat\ell-\eta\,c_{p_\theta},
--   $$
--   where $\hat\ell=M(p_\theta)^{-1}X_0Y$. The distribution $p_{\tilde\theta}$ is the exponential-weights update of $p_\theta$ with the surrogate loss $Z(x)=z^\top x$ (Eq. (15)).
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Algorithm 1, line 10, p.12

import Mathlib
import Definitions.Def_MSetBandit_lossEst
import Definitions.Def_MSetBandit_cvec

namespace MSetBandit

/-- **The multiplicative-weights parameter `θ̃_{t+1} = θ_t − η z_t`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Algorithm 1,
line 10, p.12: `z_t ← ℓ̂_t − η c_t`, `θ̃_{t+1} ← θ_t − η z_t`, `p̃_{t+1} ← p_{θ̃_{t+1}}`.

`mwuParam η θ X₀ Y` is `θ − η (ℓ̂ − η c_{p_θ})` with `ℓ̂ = lossEst θ X₀ Y`. -/
noncomputable def mwuParam {d m : ℕ} (η : ℝ) (θ : Fin d → ℝ) (X₀ : Action d m) (Y : ℝ) :
    Fin d → ℝ :=
  θ - η • (lossEst θ X₀ Y - η • cvec (wdist (m := m) θ))

end MSetBandit


