-- Prove2me | solution 1 for ActuarialValuation.decrementExpectedBenefit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:38.158477+00:00
-- url     : https://prove2.me/submissions/3c9b041f-19be-40f3-b49d-401cc19d300b

import Mathlib
import Definitions.Def_actuarial_decrementExpectedBenefit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (q : J → ℝ)
  :
  decrementExpectedBenefit q (fun _ => 0) = 0 := by
  classical
  simp [decrementExpectedBenefit]
