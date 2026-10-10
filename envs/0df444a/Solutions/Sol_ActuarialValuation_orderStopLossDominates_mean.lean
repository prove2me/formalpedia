-- Prove2me | solution 1 for ActuarialValuation.orderStopLossDominates_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:25.077782+00:00
-- url     : https://prove2.me/submissions/36a24a44-0c52-4cce-ad66-6a4e27027262

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossDominates
import Definitions.Def_actuarial_orderAggregateMean
import Definitions.Def_actuarial_orderStopLossPremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


open ActuarialValuation

theorem solution (f g : ℕ → ℝ) (B : ℕ)
  (h : orderStopLossDominates f g B) :
  orderAggregateMean f B ≤ orderAggregateMean g B := by
  have hz : ∀ w : ℕ → ℝ, orderStopLossPremium w B 0 = orderAggregateMean w B := by
    intro w
    show (∑ s ∈ Finset.range (B + 1), ((s - 0 : ℕ) : ℝ) * w s) =
      (∑ s ∈ Finset.range (B + 1), (s : ℝ) * w s)
    simp only [Nat.sub_zero]
  calc orderAggregateMean f B = orderStopLossPremium f B 0 := (hz f).symm
    _ ≤ orderStopLossPremium g B 0 := h 0
    _ = orderAggregateMean g B := hz g
