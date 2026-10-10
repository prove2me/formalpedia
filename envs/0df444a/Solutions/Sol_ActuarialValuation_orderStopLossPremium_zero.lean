-- Prove2me | solution 1 for ActuarialValuation.orderStopLossPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:22.638504+00:00
-- url     : https://prove2.me/submissions/942711a9-e208-4544-b482-3d6130d03951

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossPremium
import Definitions.Def_actuarial_orderAggregateMean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B : ℕ) :
  orderStopLossPremium w B 0 = orderAggregateMean w B := by
  show (∑ s ∈ Finset.range (B + 1), ((s - 0 : ℕ) : ℝ) * w s) =
    (∑ s ∈ Finset.range (B + 1), (s : ℝ) * w s)
  simp only [Nat.sub_zero]
