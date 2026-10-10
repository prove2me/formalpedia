-- Prove2me | solution 1 for ActuarialValuation.discountedAnnualGainSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:12.141186+00:00
-- url     : https://prove2.me/submissions/fd78c219-f0bf-4c12-bc1d-96c1d603ef47

import Mathlib
import Definitions.Def_actuarial_discountedAnnualGainSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (G : ℕ → Ω → ℝ)
    (v : ℝ) (n : ℕ) (ω : Ω) :
    discountedAnnualGainSum G v (n + 1) ω =
      discountedAnnualGainSum G v n ω + v ^ n * G n ω := by
  simp [discountedAnnualGainSum, Finset.sum_range_succ]
