-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_estimationLoss
-- name    : WassersteinDRO_Shrinkage_estimationLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:48:23.095652+00:00
-- url     : https://prove2.me/theorems/c59ab2cb-62f6-459b-9930-f79ca6e82bae
-- title:
--   Prediction-error loss of an estimator
-- statement:
--   The prediction-error loss of an estimator $\psi : \mathbb{R}^{m_y}\to\mathbb{R}^{m_x}$ applied
--   to a sample $\xi=(x,y)$ is $\|x-\psi(y)\|_2^2$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, p. 29, integrand of eq. (35)

import Mathlib

namespace WassersteinDRO.Shrinkage

/-- The prediction-error loss `‖x-ψ(y)‖₂²` of an estimator `ψ : R^{my} → R^{mx}` applied to a
sample `ξ = (x,y) ∈ R^{mx}×R^{my}`, Kuhn et al. 2019, p. 29, integrand of eq. (35). -/
noncomputable def estimationLoss {mx my : ℕ}
    (ψ : EuclideanSpace ℝ (Fin my) → EuclideanSpace ℝ (Fin mx))
    (ξ : EuclideanSpace ℝ (Fin mx ⊕ Fin my)) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin mx) ℝ).symm (fun i => ξ (Sum.inl i)) -
      ψ ((EuclideanSpace.equiv (Fin my) ℝ).symm (fun i => ξ (Sum.inr i)))‖ ^ 2

end WassersteinDRO.Shrinkage


