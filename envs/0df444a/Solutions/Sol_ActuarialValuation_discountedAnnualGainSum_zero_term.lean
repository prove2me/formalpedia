-- Prove2me | solution 1 for ActuarialValuation.discountedAnnualGainSum_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:41:25.400621+00:00
-- url     : https://prove2.me/submissions/a77714a3-efdf-41a5-b586-2d445f4aa73a

import Mathlib
import Definitions.Def_actuarial_discountedAnnualGainSum
open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (G : ℕ → Ω → ℝ) (v : ℝ) (ω : Ω)
  :
  discountedAnnualGainSum G v 0 ω = 0 := by
  simp [discountedAnnualGainSum]

