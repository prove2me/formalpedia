-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_nominalRisk
-- name    : WassersteinDRO_Shrinkage_nominalRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:47:49.295048+00:00
-- url     : https://prove2.me/theorems/d1701173-afce-4ff1-b4a2-1c65f54de64d
-- title:
--   Nominal risk of a loss function
-- statement:
--   The nominal risk of a loss function $\ell$ under a distribution $Q$ is $R(Q,\ell) =
--   E_Q[\ell(\xi)]$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, implicit throughout Section 1

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Shrinkage

/-- The nominal risk of a loss function `ℓ` under a distribution `Q`, Kuhn et al. 2019,
implicit throughout Section 1: `R(Q,ℓ) = E_Q[ℓ(ξ)]`. Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Shrinkage_psdSqrt` for why. -/
noncomputable def nominalRisk {mx my : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my)))
    (ℓ : EuclideanSpace ℝ (Fin mx ⊕ Fin my) → ℝ) : ℝ :=
  ∫ x, ℓ x ∂Q

end WassersteinDRO.Shrinkage


