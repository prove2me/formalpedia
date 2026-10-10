-- Prove2me | solution 1 for ActuarialValuation.annualDecrementLaw_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:31.012162+00:00
-- url     : https://prove2.me/submissions/9b517bc4-5f84-40b9-8846-e49efb333ab4

import Mathlib
import Definitions.Def_actuarial_isAnnualDecrementLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (p : ℝ) (q : J → ℝ)
  (h : isAnnualDecrementLaw p q)
  :
  p + (∑ j : J, q j) = 1 := by
  exact h.2.2
