-- Prove2me | solution 1 for ActuarialAnnuities.udd_due_trapezoid_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:45:16.796976+00:00
-- url     : https://prove2.me/submissions/278c70cd-a4f9-46b1-81c0-f8679f4cb3e2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bUDDTrapezoidPV
import Definitions.Def_actuarial_bTotal
import Theorems.Thm_ActuarialAnnuities_udd_due_trapezoid_exact
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h m : ℕ) (p : ℕ → ℝ)
    (hm : 0 < m) (hp : ∀ k, 0 ≤ p k) (ht : bTotal h p = 1) :
    0 ≤ bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p -
      bUDDTrapezoidPV h p
    ∧ bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p -
      bUDDTrapezoidPV h p ≤ 1/(2*(m : ℝ)) := by
  classical
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < 2*(m : ℝ) := by positivity
  have hS0 : bSurvival h p 0 = 1 := by
    simpa [bSurvival, bTotal, bAlive] using ht
  have hSh : bSurvival h p h = p h := by
    unfold bSurvival
    rw [Finset.sum_range_succ]
    have hzero :
        (∑ k ∈ Finset.range h, p k*bAlive k h) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hnot : ¬ h ≤ k := Nat.not_le_of_gt (Finset.mem_range.mp hk)
      simp [bAlive,hnot]
    rw [hzero]
    simp [bAlive]
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range h, p k := by
    apply Finset.sum_nonneg
    intro k hk
    exact hp k
  have htotal : (∑ k ∈ Finset.range h, p k)+p h=1 := by
    simpa [bTotal,Finset.sum_range_succ] using ht
  have hmass : 0 ≤ 1-p h ∧ 1-p h ≤ 1 :=
    ⟨by linarith, by linarith [hp h]⟩
  have hdue := udd_due_trapezoid_exact h m p hm
  have hdiff :
      bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p -
        bUDDTrapezoidPV h p = (1-p h)/(2*(m : ℝ)) := by
    rw [hdue, hS0, hSh]
    ring
  rw [hdiff]
  constructor
  · exact div_nonneg hmass.1 hden.le
  · exact (div_le_div_iff_of_pos_right hden).mpr hmass.2
