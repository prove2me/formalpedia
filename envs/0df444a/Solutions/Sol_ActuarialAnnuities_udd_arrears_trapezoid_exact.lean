-- Prove2me | solution 1 for ActuarialAnnuities.udd_arrears_trapezoid_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:35:37.445207+00:00
-- url     : https://prove2.me/submissions/bee4ee39-840b-4eb6-845d-07443dc2fcf3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bUDDMicroSurvival
import Definitions.Def_actuarial_bUDDTrapezoidPV
import Theorems.Thm_ActuarialAnnuities_micro_mass_total
import Theorems.Thm_ActuarialAnnuities_udd_due_trapezoid_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h m : ℕ) (p : ℕ → ℝ) (hm : 0 < m) :
    bFractionalSurvivalPV h 0 h 0 1 m 1 (fun _ => 1) p =
      bUDDTrapezoidPV h p -
        (bSurvival h p 0-bSurvival h p h)/(2*(m : ℝ)) := by
  classical
  let S : ℕ → ℝ := bUDDMicroSurvival h m p
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hLast (n : ℕ) (w : ℕ → ℝ) : bSurvival n w n = w n := by
    unfold bSurvival
    rw [Finset.sum_range_succ]
    have hzero :
        (∑ k ∈ Finset.range n, w k * bAlive k n) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hnot : ¬n ≤ k := Nat.not_le_of_gt (Finset.mem_range.mp hk)
      simp [bAlive, hnot]
    rw [hzero]
    simp [bAlive]
  have hinit : S 0 = bSurvival h p 0 := by
    dsimp [S, bUDDMicroSurvival]
    have hmInit : bSurvival (h*m) (bUDDMicroMass h m p) 0 =
        bTotal (h*m) (bUDDMicroMass h m p) := by
      simp [bSurvival, bTotal, bAlive]
    rw [hmInit, micro_mass_total h m p hm]
    simp [bSurvival, bTotal, bAlive]
  have hend : S (h*m) = bSurvival h p h := by
    dsimp [S, bUDDMicroSurvival]
    rw [hLast (h*m) (bUDDMicroMass h m p), hLast h p]
    simp [bUDDMicroMass]
  have htel (n : ℕ) (F : ℕ → ℝ) :
      (∑ q ∈ Finset.range n, (F q-F (q+1))) = F 0-F n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hpv (d : ℕ) :
      bFractionalSurvivalPV h 0 h 0 d m 1 (fun _ => 1) p =
      ∑ q ∈ Finset.range (h*m), (1/(m : ℝ))*S (q+d) := by
    unfold bFractionalSurvivalPV bSurvivalPV
    apply Finset.sum_congr rfl
    intro q hq
    have hlt : q < h*m := Finset.mem_range.mp hq
    simp [hlt, S, bUDDMicroSurvival]
  have hdiff :
      bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p -
        bFractionalSurvivalPV h 0 h 0 1 m 1 (fun _ => 1) p =
      (S 0-S (h*m))/(m : ℝ) := by
    rw [hpv 0, hpv 1]
    simp only [Nat.add_zero]
    calc
      (∑ q ∈ Finset.range (h*m), (1/(m : ℝ))*S q) -
          (∑ q ∈ Finset.range (h*m),
            (1/(m : ℝ))*S (q+1)) =
          ∑ q ∈ Finset.range (h*m),
            (S q-S (q+1))/(m : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = (S 0-S (h*m))/(m : ℝ) := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, htel (h*m) S]
  have hdue := udd_due_trapezoid_exact h m p hm
  calc
    bFractionalSurvivalPV h 0 h 0 1 m 1 (fun _ => 1) p =
        bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p -
          (S 0-S (h*m))/(m : ℝ) := by linarith
    _ = bUDDTrapezoidPV h p +
        (bSurvival h p 0-bSurvival h p h)/(2*(m : ℝ)) -
        (bSurvival h p 0-bSurvival h p h)/(m : ℝ) := by
      rw [hdue, hinit, hend]
    _ = bUDDTrapezoidPV h p -
        (bSurvival h p 0-bSurvival h p h)/(2*(m : ℝ)) := by
      field_simp [hm0]
      ring
