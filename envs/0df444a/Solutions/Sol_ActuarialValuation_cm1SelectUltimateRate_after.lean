-- Prove2me | solution 1 for ActuarialValuation.cm1SelectUltimateRate_after
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:51.000145+00:00
-- url     : https://prove2.me/submissions/19507a8e-ae9d-44fa-999d-5478fd53202b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SelectUltimateRate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (select : ℕ → ℕ → ℝ) (ultimate : ℕ → ℝ) (x k t : ℕ) (h : k ≤ t) : cm1SelectUltimateRate select ultimate x k t = ultimate (x+t) := by
  have ht : ¬ t < k := Nat.not_lt.mpr h
  simp [cm1SelectUltimateRate, ht]
