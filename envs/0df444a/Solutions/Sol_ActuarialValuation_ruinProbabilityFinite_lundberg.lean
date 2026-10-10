-- Prove2me | solution 1 for ActuarialValuation.ruinProbabilityFinite_lundberg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:59:35.429735+00:00
-- url     : https://prove2.me/submissions/5c6f414a-105e-4ab8-9026-f20b315e5fbc

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite
import Definitions.Def_actuarial_ruinAdjustmentMoment
import Definitions.Def_actuarial_ruinExponentialBound
import Definitions.Def_actuarial_ruinNextSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ) (R : ℝ)
  (hw : ∀ k, 0 ≤ w k) (hR : 0 ≤ R)
  (hmoment : ruinAdjustmentMoment w B c R ≤ 1) :
  ruinProbabilityFinite w B c n u ≤ ruinExponentialBound R u := by
  induction n generalizing u with
  | zero =>
      by_cases hu : u < 0
      · simp only [ruinProbabilityFinite, if_pos hu]
        unfold ruinExponentialBound
        apply Real.one_le_exp_iff.mpr
        apply neg_nonneg.mpr
        exact mul_nonpos_of_nonneg_of_nonpos hR (by exact_mod_cast le_of_lt hu)
      · simp only [ruinProbabilityFinite, if_neg hu]
        exact le_of_lt (Real.exp_pos _)
  | succ n ih =>
      by_cases hu : u < 0
      · simp only [ruinProbabilityFinite, if_pos hu]
        unfold ruinExponentialBound
        apply Real.one_le_exp_iff.mpr
        apply neg_nonneg.mpr
        exact mul_nonpos_of_nonneg_of_nonpos hR (by exact_mod_cast le_of_lt hu)
      · simp only [ruinProbabilityFinite, if_neg hu]
        have htransition (k : ℕ) :
            ruinExponentialBound R (ruinNextSurplus u c k) =
              ruinExponentialBound R u *
                Real.exp (R * ((k : ℝ) - (c : ℝ))) := by
          unfold ruinExponentialBound ruinNextSurplus
          push_cast
          rw [← Real.exp_add]
          congr 1
          ring
        have hweighted :
            (∑ k ∈ Finset.range (B + 1),
              w k * ruinExponentialBound R (ruinNextSurplus u c k)) =
              ruinExponentialBound R u * ruinAdjustmentMoment w B c R := by
          calc
            _ = ∑ k ∈ Finset.range (B + 1),
                  ruinExponentialBound R u *
                    (w k * Real.exp (R * ((k : ℝ) - (c : ℝ)))) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [htransition k]
                  ring
            _ = ruinExponentialBound R u *
                  ∑ k ∈ Finset.range (B + 1),
                    w k * Real.exp (R * ((k : ℝ) - (c : ℝ))) := by
                  rw [← Finset.mul_sum]
            _ = _ := rfl
        calc
          (∑ k ∈ Finset.range (B + 1),
              w k * ruinProbabilityFinite w B c n
                (ruinNextSurplus u c k))
              ≤ ∑ k ∈ Finset.range (B + 1),
                  w k * ruinExponentialBound R (ruinNextSurplus u c k) := by
                apply Finset.sum_le_sum
                intro k hk
                exact mul_le_mul_of_nonneg_left
                  (ih (ruinNextSurplus u c k)) (hw k)
          _ = ruinExponentialBound R u * ruinAdjustmentMoment w B c R := hweighted
          _ ≤ ruinExponentialBound R u * 1 := by
                apply mul_le_mul_of_nonneg_left hmoment
                exact le_of_lt (Real.exp_pos _)
          _ = ruinExponentialBound R u := by simp
