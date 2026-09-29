-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_meanVector
-- name    : WassersteinDRO_Shrinkage_meanVector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:44:44.268891+00:00
-- url     : https://prove2.me/theorems/198143cf-2d57-4ecd-b8f5-805adfbed578
-- title:
--   Mean vector of a probability measure on the signal-observation space
-- statement:
--   The mean vector of a probability measure $Q$ on $\mathbb{R}^{m_x}\times\mathbb{R}^{m_y}$ is
--   $E_Q[\xi] = \int \xi \, dQ(\xi)$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, used throughout

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Shrinkage

/-- The mean vector of a probability measure `Q` on the signal-observation space
`R^{mx} × R^{my}` (represented as `EuclideanSpace ℝ (Fin mx ⊕ Fin my)`), `E_Q[ξ]`. Redefined
locally in this chapter's own namespace; see `Def_WassersteinDRO_Shrinkage_psdSqrt` for why. -/
noncomputable def meanVector {mx my : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my))) :
    EuclideanSpace ℝ (Fin mx ⊕ Fin my) :=
  ∫ x, x ∂Q

end WassersteinDRO.Shrinkage


