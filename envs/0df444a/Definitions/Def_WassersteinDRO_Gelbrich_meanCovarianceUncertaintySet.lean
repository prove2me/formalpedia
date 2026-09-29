-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_meanCovarianceUncertaintySet
-- name    : WassersteinDRO_Gelbrich_meanCovarianceUncertaintySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:24:25.983814+00:00
-- url     : https://prove2.me/theorems/e92cfee4-4cd4-4780-9bda-da5c3ad86805
-- title:
--   Mean-covariance uncertainty set $U_\varepsilon(\hat\mu,\hat\Sigma)$
-- statement:
--   The mean-covariance uncertainty set is
--   $U_\varepsilon(\hat\mu,\hat\Sigma) = \{(\mu,\Sigma) \in \mathbb{R}^m \times S^m_+ :
--   \|\hat\mu-\mu\|_2^2 + \mathrm{Tr}[\hat\Sigma+\Sigma-2(\hat\Sigma^{1/2}\Sigma\hat\Sigma^{1/2})^{1/2}]
--   \le \varepsilon^2\}$, where $\Sigma^{1/2}$ is the positive-semidefinite matrix square root.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, displayed equation, p. 16, immediately preceding Proposition 1

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt

namespace WassersteinDRO.Gelbrich

/-- The mean-covariance uncertainty set `U_ε(µ̂,Ŝ)`, Kuhn et al. 2019, p. 16, displayed
equation immediately preceding Proposition 1:
`U_ε(µ̂,Ŝ) = {(µ,S) ∈ R^m × S^m_+ : ‖µ̂-µ‖² + Tr[Ŝ+S-2(Ŝ^{1/2}SŜ^{1/2})^{1/2}] ≤ ε²}`. -/
def meanCovarianceUncertaintySet {m : ℕ} (ε : ℝ) (μhat : EuclideanSpace ℝ (Fin m))
    (SigmaHat : Matrix (Fin m) (Fin m) ℝ) :
    Set (EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ) :=
  {p | p.2.PosSemidef ∧
    ‖μhat - p.1‖ ^ 2 +
      (SigmaHat + p.2 - (2 : ℝ) • psdSqrt (psdSqrt SigmaHat * p.2 * psdSqrt SigmaHat)).trace ≤ ε ^ 2}

end WassersteinDRO.Gelbrich


