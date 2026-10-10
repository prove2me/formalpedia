-- Prove2me | solution 1 for ActuarialValuation.layerCededPayment_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:44:43.550658+00:00
-- url     : https://prove2.me/submissions/5da3f0fc-2c67-4a0b-9d04-701a5f9873f3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d L : ℕ) (h : x ≤ d) :
  layerCededPayment x d L = 0 := by
  dsimp [layerCededPayment, layerExcessLoss]
  simp [Nat.sub_eq_zero_of_le h]
