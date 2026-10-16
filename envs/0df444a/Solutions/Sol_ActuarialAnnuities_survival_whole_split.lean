-- Prove2me | solution 1 for ActuarialAnnuities.survival_whole_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T05:56:48.261029+00:00
-- url     : https://prove2.me/submissions/d4770101-7178-420a-8a92-5dddad6a93bd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h m delta : ℕ) (v : ℝ) (b p : ℕ → ℝ)
    (hm : m ≤ h) :
    bSurvivalPV h 0 h 0 delta v b p =
      bSurvivalPV h 0 m 0 delta v b p +
      bSurvivalPV h m (h-m) 0 delta v b p := by
  classical
  unfold bSurvivalPV
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjh : j < h := Finset.mem_range.mp hj
  have hadd : m + (h-m) = h := Nat.add_sub_of_le hm
  by_cases hjm : j < m
  · simp [hjh, hjm, hadd]
  · have hmj : m ≤ j := Nat.le_of_not_gt hjm
    simp [hjh, hjm, hmj, hadd]
