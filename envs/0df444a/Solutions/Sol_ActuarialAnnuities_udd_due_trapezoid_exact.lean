-- Prove2me | solution 1 for ActuarialAnnuities.udd_due_trapezoid_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:34:42.962976+00:00
-- url     : https://prove2.me/submissions/11696639-7466-4a03-8b0a-c58f570f31ce

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bUDDTrapezoidPV
import Theorems.Thm_ActuarialAnnuities_micro_survival_udd

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h m : ℕ) (p : ℕ → ℝ) (hm : 0 < m) :
    bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p =
    bUDDTrapezoidPV h p +
      (bSurvival h p 0-bSurvival h p h)/(2*(m : ℝ)) := by
  classical
  let S : ℕ → ℝ := bSurvival h p
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hblocks (F : ℕ → ℝ) (n : ℕ) :
      (∑ q ∈ Finset.range (n*m), F q) =
        ∑ j ∈ Finset.range n, ∑ r ∈ Finset.range m, F (j*m+r) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (∑ q ∈ Finset.range ((n+1)*m), F q) =
            (∑ q ∈ Finset.range (n*m), F q) +
            (∑ r ∈ Finset.range m, F (n*m+r)) := by
          conv_lhs =>
            rw [show (n+1)*m = n*m+m by ring, Finset.sum_range_add]
        _ = ∑ j ∈ Finset.range (n+1),
              ∑ r ∈ Finset.range m, F (j*m+r) := by
          rw [ih, Finset.sum_range_succ]
  have hsumAffine (n : ℕ) (A B : ℝ) :
      (∑ r ∈ Finset.range n, (A+(r : ℝ)*B)) =
        (n : ℝ)*A + ((n : ℝ)*((n : ℝ)-1)/2)*B := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have htel (n : ℕ) (F : ℕ → ℝ) :
      (∑ j ∈ Finset.range n, (F j-F (j+1))) = F 0-F n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hPV : bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p =
      ∑ q ∈ Finset.range (h*m),
        (1/(m : ℝ))*bUDDMicroSurvival h m p q := by
    unfold bFractionalSurvivalPV bSurvivalPV
    apply Finset.sum_congr rfl
    intro q hq
    have hlt : q < h*m := Finset.mem_range.mp hq
    simp [hlt, bUDDMicroSurvival]
  have hblockPV (j : ℕ) (hj : j < h) :
      (∑ r ∈ Finset.range m,
        (1/(m : ℝ))*bUDDMicroSurvival h m p (j*m+r)) =
      (S j+S (j+1))/2 + (S j-S (j+1))/(2*(m : ℝ)) := by
    have hterm (r : ℕ) (hr : r < m) :
        (1/(m : ℝ))*bUDDMicroSurvival h m p (j*m+r) =
          S j/(m : ℝ) +
          (r : ℝ)*((S (j+1)-S j)/((m : ℝ)^2)) := by
      have hmul : (j+1)*m ≤ h*m :=
        Nat.mul_le_mul_right m (Nat.succ_le_of_lt hj)
      have hlt : j*m+r < (j+1)*m := by
        rw [Nat.succ_mul]
        omega
      have hq : j*m+r < h*m := lt_of_lt_of_le hlt hmul
      have hdiv : (j*m+r)/m = j := by
        rw [show j*m+r = m*j+r by ring, Nat.mul_add_div hm]
        simp [Nat.div_eq_of_lt hr]
      have hmod : (j*m+r)%m = r := by
        have heq := Nat.mod_add_div (j*m+r) m
        rw [hdiv, mul_comm m j] at heq
        omega
      rw [micro_survival_udd h m (j*m+r) p hm hq, hdiv, hmod]
      dsimp [S]
      unfold bUDD
      field_simp [hm0]
      ring
    calc
      (∑ r ∈ Finset.range m,
        (1/(m : ℝ))*bUDDMicroSurvival h m p (j*m+r)) =
        ∑ r ∈ Finset.range m,
          ((S j/(m : ℝ)) +
          (r : ℝ)*((S (j+1)-S j)/((m : ℝ)^2))) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hterm r (Finset.mem_range.mp hr)
      _ = (m : ℝ)*(S j/(m : ℝ)) +
          ((m : ℝ)*((m : ℝ)-1)/2)*
          ((S (j+1)-S j)/((m : ℝ)^2)) :=
        hsumAffine m _ _
      _ = (S j+S (j+1))/2 + (S j-S (j+1))/(2*(m : ℝ)) := by
        field_simp [hm0]
        ring
  have hcorr :
      (∑ j ∈ Finset.range h,
        (S j-S (j+1))/(2*(m : ℝ))) =
      (S 0-S h)/(2*(m : ℝ)) := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, htel h S]
  calc
    bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p =
        ∑ j ∈ Finset.range h, ∑ r ∈ Finset.range m,
          (1/(m : ℝ))*bUDDMicroSurvival h m p (j*m+r) := by
      rw [hPV, hblocks]
    _ = ∑ j ∈ Finset.range h,
        ((S j+S (j+1))/2 + (S j-S (j+1))/(2*(m : ℝ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hblockPV j (Finset.mem_range.mp hj)
    _ = (∑ j ∈ Finset.range h, (S j+S (j+1))/2) +
        (∑ j ∈ Finset.range h, (S j-S (j+1))/(2*(m : ℝ))) := by
      rw [Finset.sum_add_distrib]
    _ = bUDDTrapezoidPV h p +
        (bSurvival h p 0-bSurvival h p h)/(2*(m : ℝ)) := by
      rw [hcorr]
      rfl
