-- Prove2me | solution 1 for ActuarialValuation.layerCededPayment_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:44:49.996083+00:00
-- url     : https://prove2.me/submissions/37766156-b47b-4fea-806e-8bf16adccdba

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d : ℕ) :
  layerCededPayment x d 0 = 0 := by
  simp [layerCededPayment]
