-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPayment_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:20:54.368318+00:00
-- url     : https://prove2.me/submissions/7785abd1-bb21-46f5-b96c-716c03ea4aca

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPayment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim deductible : ℕ)
  (h : deductible ≤ claim) :
  discreteStopLossPayment claim deductible = claim - deductible := by
  rfl
