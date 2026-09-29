-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_gelbrichHull
-- name    : WassersteinDRO_Gelbrich_gelbrichHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:25:11.667097+00:00
-- url     : https://prove2.me/theorems/9f9bfba2-76f9-4bcd-9705-db95b2a484f0
-- title:
--   Gelbrich hull $G_\varepsilon(\hat\mu,\hat\Sigma)$
-- statement:
--   The Gelbrich hull is $G_\varepsilon(\hat\mu,\hat\Sigma) = \{Q \in \mathcal{P}(\Xi) :
--   (E_Q[\xi], \mathrm{Cov}_Q[\xi]) \in U_\varepsilon(\hat\mu,\hat\Sigma)\}$: the set of probability
--   measures on $\Xi$ whose mean vector and covariance matrix lie in the mean-covariance
--   uncertainty set.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Definition 2, p. 17

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
import Definitions.Def_WassersteinDRO_Gelbrich_meanCovarianceUncertaintySet

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- The Gelbrich hull `G_ε(µ̂,Ŝ)`, Kuhn et al. 2019, Definition 2, p. 17: the set of
probability measures on `Ξ` whose mean and covariance lie in the mean-covariance uncertainty
set `U_ε(µ̂,Ŝ)`. -/
def gelbrichHull {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {Q | Q Set.univ = 1 ∧ Q Ξᶜ = 0 ∧
    (meanVector Q, covarianceMatrix Q) ∈ meanCovarianceUncertaintySet ε μhat SigmaHat}

end WassersteinDRO.Gelbrich


