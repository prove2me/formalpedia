-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
-- name    : WassersteinDRO_Gelbrich_covarianceMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:21:59.774986+00:00
-- url     : https://prove2.me/theorems/a00d5c61-1ffa-49e6-83f3-38cd41633e59
-- title:
--   Covariance matrix of a probability measure
-- statement:
--   The covariance matrix of a probability measure $Q$ on $\mathbb{R}^m$ is
--   $E_Q[(\xi - E_Q[\xi])(\xi - E_Q[\xi])^\top]$, the matrix whose $(i,j)$ entry is the Bochner
--   integral $\int (\xi_i - E_Q[\xi]_i)(\xi_j - E_Q[\xi]_j) \, dQ(\xi)$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, used throughout Section 2.3, e.g. Theorem 4 p. 8, Proposition 1 p. 16

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- The covariance matrix of a probability measure `Q` on `ℝ^m`,
`E_Q[(ξ-E_Q[ξ])(ξ-E_Q[ξ])^T]`, used throughout Section 2.3 of Kuhn et al. 2019 (e.g. Theorem
4, p. 8; Proposition 1, p. 16). -/
noncomputable def covarianceMatrix {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of (fun i j => ∫ x : EuclideanSpace ℝ (Fin m), (x i - meanVector Q i) * (x j - meanVector Q j) ∂Q)

end WassersteinDRO.Gelbrich


