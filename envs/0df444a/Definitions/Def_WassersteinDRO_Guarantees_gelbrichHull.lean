-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_gelbrichHull
-- name    : WassersteinDRO_Guarantees_gelbrichHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:32:48.786169+00:00
-- url     : https://prove2.me/theorems/d1d69478-5a77-460c-8d01-45911aa32484
-- title:
--   Gelbrich hull $G_\varepsilon(\hat\mu,\hat\Sigma)$
-- statement:
--   $G_\varepsilon(\hat\mu,\hat\Sigma) = \{Q \in \mathcal{P}(\Xi) : (E_Q[\xi], \mathrm{Cov}_Q[\xi])
--   \in U_\varepsilon(\hat\mu,\hat\Sigma)\}$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Definition 2, p. 17

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_WassersteinDRO_Guarantees_meanCovarianceUncertaintySet

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The Gelbrich hull `G_ε(µ̂,Ŝ)`, Kuhn et al. 2019, Definition 2, p. 17. Redefined locally
in this chapter's own namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
def gelbrichHull {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {Q | Q Set.univ = 1 ∧ Q Ξᶜ = 0 ∧
    (meanVector Q, covarianceMatrix Q) ∈ meanCovarianceUncertaintySet ε μhat SigmaHat}

end WassersteinDRO.Guarantees


