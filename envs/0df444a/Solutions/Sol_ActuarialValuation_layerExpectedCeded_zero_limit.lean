-- Prove2me | solution 1 for ActuarialValuation.layerExpectedCeded_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:45:22.088191+00:00
-- url     : https://prove2.me/submissions/bf4863ec-8798-413d-acd2-1e1a3aed7902

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerCededPayment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B d : ℕ) :
  layerExpectedCeded w B d 0 = 0 := by
  simp [layerExpectedCeded, layerCededPayment]
