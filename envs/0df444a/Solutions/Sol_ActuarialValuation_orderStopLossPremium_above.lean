-- Prove2me | solution 1 for ActuarialValuation.orderStopLossPremium_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:23.230992+00:00
-- url     : https://prove2.me/submissions/ee015c57-018b-48f8-85cd-54cb5bc8d2cf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossPremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B d : ℕ) (h : B ≤ d) :
  orderStopLossPremium w B d = 0 := by
  show (∑ s ∈ Finset.range (B + 1), ((s - d : ℕ) : ℝ) * w s) = 0
  apply Finset.sum_eq_zero
  intro s hs
  have hle : s ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hsd : s - d = 0 := Nat.sub_eq_zero_of_le (le_trans hle h)
  rw [hsd]
  simp
