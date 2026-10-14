-- Prove2me | solution 1 for ActuarialValuation.tailCDF_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:06:02.925558+00:00
-- url     : https://prove2.me/submissions/fdf5d9db-edcb-4bfc-8aae-58c9d4436dec

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailMass
import Definitions.Def_actuarial_tailCDF
import Definitions.Def_actuarial_tailUpperMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n t : ℕ) :
    tailCDF p n t + tailUpperMass p n t = tailMass p n := by
  unfold tailCDF tailUpperMass tailMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k ≤ t
  · have hnt : ¬ t < k := not_lt.mpr h
    simp [h, hnt]
  · have ht : t < k := by omega
    simp [h, ht]
