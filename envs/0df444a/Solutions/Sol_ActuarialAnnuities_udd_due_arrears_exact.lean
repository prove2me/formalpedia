-- Prove2me | solution 1 for ActuarialAnnuities.udd_due_arrears_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:37:39.907022+00:00
-- url     : https://prove2.me/submissions/7bc77742-1e23-46ce-ae80-7175a7d32958

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bUDDTrapezoidPV

namespace ActuarialAnnuities

theorem udd_aux_block (p : ℕ → ℝ) (m : ℕ) (hm : 0 < m) :
    ∀ h : ℕ, ∑ q ∈ Finset.range (h * m), p (q / m) / (m : ℝ) = ∑ k ∈ Finset.range h, p k := by
  intro h
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    have : ∀ x ∈ Finset.range m, p ((h * m + x) / m) / (m : ℝ) = p h / (m : ℝ) := by
      intro x hx
      simp at hx
      rw [show (h * m + x) / m = h by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hx, zero_add]]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp

end ActuarialAnnuities

open ActuarialAnnuities

theorem solution (h m : ℕ) (p : ℕ → ℝ) (hm : 0 < m) :
  bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p -
    bFractionalSurvivalPV h 0 h 0 1 m 1 (fun _ => 1) p =
      (bSurvival h p 0-bSurvival h p h)/(m : ℝ) := by
  have hsv : ∀ (H δ : ℕ) (c : ℝ) (q : ℕ → ℝ),
      bSurvivalPV H 0 H 0 δ 1 (fun _ => c) q = ∑ j ∈ Finset.range H, c * bSurvival H q (j + δ) := by
    intro H δ c q; unfold bSurvivalPV; apply Finset.sum_congr rfl; intro j hj
    simp at hj; simp [hj]
  unfold bFractionalSurvivalPV
  simp only [zero_mul]
  rw [hsv, hsv, ← Finset.sum_sub_distrib]
  simp only [add_zero, ← mul_sub]
  rw [← Finset.mul_sum, Finset.sum_range_sub' (fun j => bSurvival (h * m) (bUDDMicroMass h m p) j)]
  have hS0 : bSurvival (h * m) (bUDDMicroMass h m p) 0 = bSurvival h p 0 := by
    unfold bSurvival bAlive
    simp only [Nat.zero_le, if_true, mul_one]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    unfold bUDDMicroMass
    rw [if_neg (lt_irrefl _), if_pos rfl]
    congr 1
    rw [← udd_aux_block p m hm h]
    apply Finset.sum_congr rfl; intro q hq
    rw [if_pos (Finset.mem_range.mp hq)]
  have hSH : bSurvival (h * m) (bUDDMicroMass h m p) (h * m) = bSurvival h p h := by
    unfold bSurvival bAlive
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · unfold bUDDMicroMass; simp
    · intro k hk; simp at hk; simp [show ¬ (h ≤ k) by omega]
    · intro k hk; simp at hk; simp [show ¬ (h * m ≤ k) by omega]
  rw [hS0, hSH]
  ring
