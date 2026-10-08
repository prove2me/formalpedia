-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_gelbrichHull_v2
-- name    : WassersteinDRO_Guarantees_gelbrichHull_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:19:43.504331+00:00
-- url     : https://prove2.me/theorems/071e9fad-5caf-4de4-97f5-76bbdd5b15bb
-- title:
--   Gelbrich hull $\mathcal{G}_\varepsilon(\hat\mu,\hat\Sigma)$ (finite second moments)
-- statement:
--   The Gelbrich hull (Definition 2): $$\mathcal{G}_\varepsilon(\hat\mu,\hat\Sigma) = \big\{Q \in \mathcal{P}(\Xi) : (\mathbb{E}_Q[\xi],\, \mathbb{E}_Q[(\xi-\mathbb{E}_Q[\xi])(\xi-\mathbb{E}_Q[\xi])^\top]) \in \mathcal{U}_\varepsilon(\hat\mu,\hat\Sigma)\big\},$$ the probability distributions supported on $\Xi$ whose mean vector and covariance matrix lie in the mean–covariance uncertainty set. Membership presupposes that $Q$ has a mean vector and a covariance matrix, i.e. $\mathbb{E}_Q[\|\xi\|^2] < \infty$ (p. 18); this finite-second-moment condition is recorded explicitly. It replaces the `gelbrichHull` that omitted it and so admitted distributions with infinite second moments through the junk value $0$ of a non-integrable Bochner integral.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), Definition 2, p. 17 (and the description on p. 18)

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_WassersteinDRO_Guarantees_meanCovarianceUncertaintySet

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The Gelbrich hull `G_ε(µ̂,Σ̂)`, Kuhn et al. 2019, Definition 2, p. 17:
`G_ε(µ̂,Σ̂) = {Q ∈ P(Ξ) : (E_Q[ξ], E_Q[(ξ-E_Q[ξ])(ξ-E_Q[ξ])ᵀ]) ∈ U_ε(µ̂,Σ̂)}`, the
probability distributions supported on `Ξ` whose mean vector and covariance matrix lie in the
mean-covariance uncertainty set. Membership presupposes that `Q` *has* a mean vector and a
covariance matrix, i.e. a finite second moment `E_Q[‖ξ‖²] < ∞` (the paper, p. 18: the hull
"contains all distributions supported on `Ξ` whose mean vectors and covariance matrices fall
into `U_ε`"); this is recorded as the explicit condition `Integrable (fun ξ => ‖ξ‖^2) Q`.
This replaces the retired `gelbrichHull`, which omitted the condition and therefore admitted
distributions with infinite second moments through the junk value `0` that Mathlib's Bochner
integral returns for a non-integrable integrand in `meanVector`/`covarianceMatrix`. -/
def gelbrichHull {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {Q | Q Set.univ = 1 ∧ Q Ξᶜ = 0 ∧ Integrable (fun ξ => ‖ξ‖ ^ 2) Q ∧
    (meanVector Q, covarianceMatrix Q) ∈ meanCovarianceUncertaintySet ε μhat SigmaHat}

end WassersteinDRO.Guarantees


