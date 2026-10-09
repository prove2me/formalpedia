-- Prove2me | solution 1 for ActuarialValuation.flatInterest_discount_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:01:58.492801+00:00
-- url     : https://prove2.me/submissions/24948343-3c72-4410-a307-cfff072bad24

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution (i : ℝ) (hi : 0 < i)
    :
    0 < (1 / (1 + i) : ℝ) ∧ (1 / (1 + i) : ℝ) < 1 := by
  have hden : 0 < 1 + i := by linarith
  constructor
  · positivity
  · apply (div_lt_one hden).mpr
    linarith
