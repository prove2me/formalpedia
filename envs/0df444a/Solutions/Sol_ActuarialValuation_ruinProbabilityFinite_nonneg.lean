-- Prove2me | solution 1 for ActuarialValuation.ruinProbabilityFinite_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:52:25.475982+00:00
-- url     : https://prove2.me/submissions/a0b52bfc-0293-4432-bd5d-76b2c300dc8d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ)
  (hw : ∀ k, 0 ≤ w k) :
  0 ≤ ruinProbabilityFinite w B c n u := by
  induction n generalizing u with
  | zero =>
      simp only [ruinProbabilityFinite]
      split_ifs <;> norm_num
  | succ n ih =>
      simp only [ruinProbabilityFinite]
      split_ifs with h
      · norm_num
      · apply Finset.sum_nonneg
        intro k hk
        exact mul_nonneg (hw k) (ih (ruinNextSurplus u c k))
