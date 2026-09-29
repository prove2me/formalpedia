-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_nominalRisk
-- name    : WassersteinDRO_Gelbrich_nominalRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:25:25.489986+00:00
-- url     : https://prove2.me/theorems/29e6e9fa-2934-47d3-8621-f3856fcd4d63
-- title:
--   Nominal risk of a loss function
-- statement:
--   The nominal risk of a loss function $\ell$ under a distribution $Q$ is
--   $R(Q,\ell) = E_Q[\ell(\xi)] = \int \ell(\xi) \, dQ(\xi)$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, implicit throughout Section 1

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- The nominal risk of a loss function `ℓ` under a distribution `Q`, Kuhn et al. 2019,
implicit throughout Section 1: `R(Q,ℓ) = E_Q[ℓ(ξ)]`. Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Gelbrich_wassersteinDistance` for why. -/
noncomputable def nominalRisk {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ :=
  ∫ x, ℓ x ∂Q

end WassersteinDRO.Gelbrich


