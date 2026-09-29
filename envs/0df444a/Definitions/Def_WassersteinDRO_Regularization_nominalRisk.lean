-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_nominalRisk
-- name    : WassersteinDRO_Regularization_nominalRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:39:00.593404+00:00
-- url     : https://prove2.me/theorems/c918856c-3f86-4155-807b-1ca8ebcb6454
-- title:
--   Nominal risk of a loss function
-- statement:
--   The nominal risk of a loss function $\ell$ under a distribution $Q$ is
--   $R(Q,\ell) = E_Q[\ell(\xi)] = \int \ell(\xi) \, dQ(\xi)$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, implicit throughout Section 1

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- The nominal risk of a loss function `ℓ` under a distribution `Q`, Kuhn et al. 2019,
implicit throughout Section 1: `R(Q,ℓ) = E_Q[ℓ(ξ)]`. Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Regularization_wassersteinDistance` for why. -/
noncomputable def nominalRisk {E : Type*} [MeasurableSpace E] (Q : Measure E) (ℓ : E → ℝ) : ℝ :=
  ∫ x, ℓ x ∂Q

end WassersteinDRO.Regularization


