-- Prove2me | solution 1 for ActuarialValuation.orderStopLossDominates_refl
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:22.069521+00:00
-- url     : https://prove2.me/submissions/3a9db48f-5681-4cfb-8083-b6fcc3a27f4f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossDominates
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B : ℕ) :
  orderStopLossDominates w w B := by
  show ∀ d : ℕ, orderStopLossPremium w B d ≤ orderStopLossPremium w B d
  exact fun d => le_refl _
