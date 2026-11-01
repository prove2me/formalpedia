-- Prove2me | Definitions.Def_LatentMixDRO_IsEmpMinimizer
-- name    : LatentMixDRO_IsEmpMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:44.837873+00:00
-- url     : https://prove2.me/theorems/28e87c2c-8bf8-46d7-8cf1-0caf442a55bf
-- title:
--   $\hat\theta$ is an empirical minimizer of (16)
-- statement:
--   A parameter $\hat\theta\in\Theta$ is an **empirical minimizer** when it attains the minimum over $\Theta$ of the objective of (16); that is, $\hat\theta\in\operatorname{argmin}_{\theta\in\Theta}$ of that objective, the estimator $\hat\theta^{\mathrm{rob}}_{n,\epsilon}$ of the paper.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (16), p.11

import Mathlib
import Definitions.Def_LatentMixDRO_empObj

namespace LatentMixDRO

/-- `θhat` is an empirical minimizer of (16): `θ̂^rob_{n,ε} ∈ argmin_{θ ∈ Θ} empObj`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (16), p.11. -/
def IsEmpMinimizer {d n : ℕ} {Θ : Type*} (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ)
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (p ε L α₀ M : ℝ) (θhat : Θ) : Prop :=
  ∀ θ, empObj ω ℓ p ε L α₀ M θhat ≤ empObj ω ℓ p ε L α₀ M θ

end LatentMixDRO


