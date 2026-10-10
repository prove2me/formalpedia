-- Prove2me | solution 1 for ActuarialValuation.annualDecrementLaw_cause_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:23.633198+00:00
-- url     : https://prove2.me/submissions/fc8f268a-5820-49b6-940b-16ac722a5429

import Mathlib
import Definitions.Def_actuarial_isAnnualDecrementLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (p : ℝ) (q : J → ℝ)
  (h : isAnnualDecrementLaw p q) (j : J)
  :
  0 ≤ q j := by
  exact h.2.1 j
