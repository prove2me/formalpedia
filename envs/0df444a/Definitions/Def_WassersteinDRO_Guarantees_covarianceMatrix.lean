-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
-- name    : WassersteinDRO_Guarantees_covarianceMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:30:39.453984+00:00
-- url     : https://prove2.me/theorems/824ec222-78cc-4456-8385-eae91c34ad0e
-- title:
--   Covariance matrix of a probability measure
-- statement:
--   The covariance matrix of a probability measure $Q$ on $\mathbb{R}^m$ is
--   $E_Q[(\xi-E_Q[\xi])(\xi-E_Q[\xi])^\top]$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, used throughout

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The covariance matrix of a probability measure `Q` on `ℝ^m`,
`E_Q[(ξ-E_Q[ξ])(ξ-E_Q[ξ])^T]`. Redefined locally in this chapter's own namespace; see
`Def_WassersteinDRO_Guarantees_meanVector` for why. -/
noncomputable def covarianceMatrix {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of (fun i j => ∫ x : EuclideanSpace ℝ (Fin m), (x i - meanVector Q i) * (x j - meanVector Q j) ∂Q)

end WassersteinDRO.Guarantees


