-- Prove2me | solution 2 for ActuarialValuation.annualDecrementLaw_survival_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:17.740987+00:00
-- url     : https://prove2.me/submissions/97c8e1d6-21a6-4bea-9359-db36ad690943

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
  0 ≤ p := by
  exact h.1
