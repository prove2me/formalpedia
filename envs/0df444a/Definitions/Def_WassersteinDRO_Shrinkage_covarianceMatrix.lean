-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_covarianceMatrix
-- name    : WassersteinDRO_Shrinkage_covarianceMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:45:21.929228+00:00
-- url     : https://prove2.me/theorems/e305644e-a101-475b-bac8-a8a3e5c95aee
-- title:
--   Covariance matrix of a probability measure on the signal-observation space
-- statement:
--   The covariance matrix of a probability measure $Q$ on $\mathbb{R}^{m_x}\times\mathbb{R}^{m_y}$
--   is $E_Q[(\xi-E_Q[\xi])(\xi-E_Q[\xi])^\top]$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, used throughout

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_meanVector

open MeasureTheory

namespace WassersteinDRO.Shrinkage

/-- The covariance matrix of a probability measure `Q` on `R^{mx} × R^{my}`,
`E_Q[(ξ-E_Q[ξ])(ξ-E_Q[ξ])^T]`. Redefined locally in this chapter's own namespace; see
`Def_WassersteinDRO_Shrinkage_psdSqrt` for why. -/
noncomputable def covarianceMatrix {mx my : ℕ}
    (Q : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my))) :
    Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ :=
  Matrix.of (fun i j =>
    ∫ x : EuclideanSpace ℝ (Fin mx ⊕ Fin my), (x i - meanVector Q i) * (x j - meanVector Q j) ∂Q)

end WassersteinDRO.Shrinkage


