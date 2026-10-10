-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPayment_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:21:00.180746+00:00
-- url     : https://prove2.me/submissions/c866bd0d-0767-446b-885a-56c80d8a4491

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPayment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim deductible : ℕ) :
  min claim deductible + discreteStopLossPayment claim deductible = claim := by
  simp only [discreteStopLossPayment]
  omega
