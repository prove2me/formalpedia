-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_IsElliptical
-- name    : WassersteinDRO_Shrinkage_IsElliptical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:45:59.419973+00:00
-- url     : https://prove2.me/theorems/4fd82990-3306-418a-b133-c84f0f5440dd
-- title:
--   Elliptical probability distribution (mean/covariance record)
-- statement:
--   $Q$ is recorded as the elliptical distribution $E_g(\mu,S)$ with density generator $g$, mean
--   vector $\mu$ and covariance matrix $S$ when $Q$ is a probability measure with $E_Q[\xi]=\mu$
--   and $\mathrm{Cov}_Q[\xi]=S$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, notation p. 2, density formula Appendix A p. 30

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_meanVector
import Definitions.Def_WassersteinDRO_Shrinkage_covarianceMatrix

open MeasureTheory

namespace WassersteinDRO.Shrinkage

/-- `Q` is the elliptical distribution `E_g(μ,S)` with density generator `g`, mean `μ` and
covariance `S` (Kuhn et al. 2019, notation p. 2, density formula Appendix A p. 30), recording
only the mean/covariance facts this chapter's theorem uses — matching `02-gelbrich`'s
`IsElliptical` of the same name, redefined locally per addendum rule 5. -/
structure IsElliptical {mx my : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my))) (g : ℝ → ℝ)
    (μ : EuclideanSpace ℝ (Fin mx ⊕ Fin my)) (S : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ) :
    Prop where
  isProb : Q Set.univ = 1
  mean_eq : meanVector Q = μ
  cov_eq : covarianceMatrix Q = S

end WassersteinDRO.Shrinkage


