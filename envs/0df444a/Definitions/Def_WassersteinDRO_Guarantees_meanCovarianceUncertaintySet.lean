-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_meanCovarianceUncertaintySet
-- name    : WassersteinDRO_Guarantees_meanCovarianceUncertaintySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:31:28.829911+00:00
-- url     : https://prove2.me/theorems/7423b55c-6913-4b36-b209-a2147f48e84a
-- title:
--   Mean-covariance uncertainty set $U_\varepsilon(\hat\mu,\hat\Sigma)$
-- statement:
--   $U_\varepsilon(\hat\mu,\hat\Sigma) = \{(\mu,\Sigma) \in \mathbb{R}^m \times S^m_+ :
--   \|\hat\mu-\mu\|_2^2 + \mathrm{Tr}[\hat\Sigma+\Sigma-2(\hat\Sigma^{1/2}\Sigma\hat\Sigma^{1/2})^{1/2}]
--   \le \varepsilon^2\}$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, displayed equation, p. 16, immediately preceding Proposition 1

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_psdSqrt

namespace WassersteinDRO.Guarantees

/-- The mean-covariance uncertainty set `U_ε(µ̂,Ŝ)`, Kuhn et al. 2019, p. 16, displayed
equation immediately preceding Proposition 1. Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
def meanCovarianceUncertaintySet {m : ℕ} (ε : ℝ) (μhat : EuclideanSpace ℝ (Fin m))
    (SigmaHat : Matrix (Fin m) (Fin m) ℝ) :
    Set (EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ) :=
  {p | p.2.PosSemidef ∧
    ‖μhat - p.1‖ ^ 2 +
      (SigmaHat + p.2 - (2 : ℝ) • psdSqrt (psdSqrt SigmaHat * p.2 * psdSqrt SigmaHat)).trace ≤ ε ^ 2}

end WassersteinDRO.Guarantees


