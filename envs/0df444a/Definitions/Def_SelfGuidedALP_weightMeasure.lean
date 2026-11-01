-- Prove2me | Definitions.Def_SelfGuidedALP_weightMeasure
-- name    : SelfGuidedALP_weightMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:38.32965+00:00
-- url     : https://prove2.me/theorems/5eaf2190-36d5-4ef3-95fc-4fa4f9227ff2
-- title:
--   The measure $\rho(\theta)^{-1}\,\mathrm d\theta$ on $\Theta$
-- statement:
--   The **weight measure** is $\rho(\theta)^{-1}\,\mathrm d\theta$ on $\Theta$. Its square-integrable functions are the weighting functions of the feature-based linear program.
--
--   **Formalization Note** The density is taken in $[0,\infty]$, so it equals $+\infty$ where $\rho=0$. A function with $\int B^2/\rho<\infty$ then vanishes almost everywhere on $\{\rho=0\}$, which is the only meaning of $B/\rho$ there, and no division by zero silently returns $0$. The density never vanishes, so this measure and Lebesgue measure on $\Theta$ have the same null sets.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition EC.2, p.ec8

import Mathlib
import Definitions.Def_SelfGuidedALP_RBClass

open MeasureTheory

namespace SelfGuidedALP

/-- The measure `(1/ρ(θ)) dθ` on `Θ`, whose `L²` space is the space `ℬ` of weighting functions
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition EC.2, p.ec8).

**Formalization Note.** The density is the `ℝ≥0∞` inverse of `ρ`, so it is `∞` where `ρ = 0`: a
function with finite `∫ B²/ρ` then vanishes almost everywhere on `{ρ = 0}`, which is the only
meaning of `B/ρ` there, and no division by zero returns `0`. The density is never `0`, so this measure
and Lebesgue measure on `Θ` have the same null sets. -/
noncomputable def weightMeasure {d : ℕ} (R : RBClass d) : Measure (EuclideanSpace ℝ (Fin (d + 1))) :=
  (volume.restrict R.Θ).withDensity fun θ => (ENNReal.ofReal (R.ρ θ))⁻¹

end SelfGuidedALP


