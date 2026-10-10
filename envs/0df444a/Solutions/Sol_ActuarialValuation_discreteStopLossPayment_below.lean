-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPayment_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:20:48.340592+00:00
-- url     : https://prove2.me/submissions/7dd5a331-7348-442f-b54e-8ab85a05bf48

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPayment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim deductible : ℕ)
  (h : claim ≤ deductible) :
  discreteStopLossPayment claim deductible = 0 := by
  simpa [discreteStopLossPayment] using Nat.sub_eq_zero_of_le h
