-- Prove2me | solution 1 for ActuarialValuation.layerExcessLoss_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:44:34.815183+00:00
-- url     : https://prove2.me/submissions/f40c338a-eed9-4b8c-b711-a1a1ba729700

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d : ℕ) (h : x ≤ d) :
  layerExcessLoss x d = 0 := by
  dsimp [layerExcessLoss]
  exact Nat.sub_eq_zero_of_le h
