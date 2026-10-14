-- Prove2me | solution 1 for ActuarialValuation.svTail_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:09:32.580205+00:00
-- url     : https://prove2.me/submissions/defdca56-e6c4-4e13-b0e3-c9eb22521e06

import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n k : ℕ) (hk : k < n) : svFiniteTailMass p n k = p (k+1) + svFiniteTailMass p n (k+1) := by
  unfold svFiniteTailMass
  have hkn : k + 1 ≤ n := Nat.succ_le_iff.mpr hk
  have hn : k+1 ∉ Finset.Icc ((k+1)+1) n := by simp
  rw [← Finset.insert_Icc_succ_left_eq_Icc hkn]
  exact Finset.sum_insert hn
