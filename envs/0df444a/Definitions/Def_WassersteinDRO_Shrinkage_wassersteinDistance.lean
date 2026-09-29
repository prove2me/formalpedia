-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_wassersteinDistance
-- name    : WassersteinDRO_Shrinkage_wassersteinDistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:46:22.823542+00:00
-- url     : https://prove2.me/theorems/5dc3f0b9-ea01-4dac-9ec1-c5d4853fa421
-- title:
--   Type-$p$ Wasserstein distance
-- statement:
--   The type-$p$ Wasserstein distance between two Borel probability measures $Q,Q'$ on
--   $\mathbb{R}^{m_x}\times\mathbb{R}^{m_y}$ is $W_p(Q,Q') = \left(\inf_\pi \int \|\xi-\xi'\|^p \,
--   d\pi(\xi,\xi')\right)^{1/p}$, the infimum over couplings $\pi$ of $Q,Q'$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Definition 1, p. 3, eq. (5)

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Shrinkage

/-- The type-`p` Wasserstein distance between two Borel probability measures on `R^{mx}×R^{my}`,
Kuhn et al. 2019, Definition 1, p. 3, eq. (5). Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Shrinkage_psdSqrt` for why. -/
noncomputable def wassersteinDistance {mx my : ℕ} (p : ℝ)
    (Q Q' : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my))) : ENNReal :=
  (⨅ (π : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my) × EuclideanSpace ℝ (Fin mx ⊕ Fin my)))
      (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'),
      ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) ^ (1 / p)

end WassersteinDRO.Shrinkage


