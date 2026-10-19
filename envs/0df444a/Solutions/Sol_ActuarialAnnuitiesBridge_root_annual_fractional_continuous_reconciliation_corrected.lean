-- Prove2me | solution 1 for ActuarialAnnuitiesBridge.root_annual_fractional_continuous_reconciliation_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:55:18.509997+00:00
-- url     : https://prove2.me/submissions/6041f35b-5808-4aa6-9d3c-8e4ab0fc46a2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bFractionalExpectedPV
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bcSurvival
import Definitions.Def_actuarial_bcExpectedPV
import Definitions.Def_actuarial_bcProjectedPV
import Definitions.Def_actuarial_bcGuaranteedPV
import Definitions.Def_actuarial_bcPostGuaranteePV
import Definitions.Def_actuarial_bUDDTrapezoidPV
import Definitions.Def_actuarial_bUDD
import Definitions.Def_actuarial_bUDDMicroMass
import Definitions.Def_actuarial_bUDDMicroSurvival
import Theorems.Thm_ActuarialAnnuities_path_expectation_reconciliation
import Theorems.Thm_ActuarialAnnuities_fractional_random_expectation
import Theorems.Thm_ActuarialAnnuitiesContinuous_bc_continuous_reconciliation
import Theorems.Thm_ActuarialAnnuitiesContinuous_bc_continuous_guarantee_partition
import Theorems.Thm_ActuarialAnnuitiesBridge_bridge_micro_survival
import Theorems.Thm_ActuarialAnnuities_micro_survival_udd
import Theorems.Thm_ActuarialAnnuities_udd_due_trapezoid_exact
import Theorems.Thm_ActuarialAnnuitiesBridge_udd_micro_continuous_equals_arrears
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
theorem solution (h a n g m : ℕ) (v w rho : ℝ)
    (b p : ℕ → ℝ) (rate : ℝ → ℝ)
    (hm : 0 < m) (hp : ActuarialAnnuities.bTotal h p = 1)
    (hprob : ∀ k, 0 ≤ p k) (hv : 0 < v) (hw : 0 < w)
    (hi : IntervalIntegrable (fun t => rate t * Real.exp (-rho*t))
        volume (a : ℝ) ((a : ℝ)+(n : ℝ))) :
    (ActuarialAnnuities.bExpectedPV h a n g 0 v b p =
      ActuarialAnnuities.bSurvivalPV h a n g 0 v b p)
    ∧ (ActuarialAnnuities.bExpectedPV h a n g 1 v b p =
      ActuarialAnnuities.bSurvivalPV h a n g 1 v b p)
    ∧ (ActuarialAnnuities.bFractionalExpectedPV h a n g 0 m w b p =
      ActuarialAnnuities.bFractionalSurvivalPV h a n g 0 m w b p)
    ∧ (ActuarialAnnuitiesContinuous.bcExpectedPV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) (n : ℝ) (g : ℝ) rho rate =
      ActuarialAnnuitiesContinuous.bcProjectedPV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) (n : ℝ) (g : ℝ) rho rate)
    ∧ (ActuarialAnnuitiesContinuous.bcProjectedPV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) (n : ℝ) (g : ℝ) rho rate =
      ActuarialAnnuitiesContinuous.bcGuaranteedPV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) (n : ℝ) (g : ℝ) rho rate +
      ActuarialAnnuitiesContinuous.bcPostGuaranteePV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) (n : ℝ) (g : ℝ) rho rate)
    ∧ (ActuarialAnnuitiesContinuous.bcSurvival (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (((a*m : ℕ) : ℝ)/(m : ℝ)) =
      ActuarialAnnuities.bUDDMicroSurvival h m p (a*m))
    ∧ (ActuarialAnnuitiesContinuous.bcSurvival (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) =
      ActuarialAnnuities.bSurvival h p a)
    ∧ (ActuarialAnnuities.bFractionalSurvivalPV h 0 h 0 0 m 1
      (fun _ => 1) p = ActuarialAnnuities.bUDDTrapezoidPV h p +
      (ActuarialAnnuities.bSurvival h p 0 -
       ActuarialAnnuities.bSurvival h p h)/(2*(m : ℝ)))
    ∧ (ActuarialAnnuitiesContinuous.bcExpectedPV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) 0 (h : ℝ) 0 0 (fun _ => 1) =
      ActuarialAnnuities.bFractionalSurvivalPV h 0 h 0 1 m 1
        (fun _ => 1) p) := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hlast (N : ℕ) (u : ℕ → ℝ) :
      ActuarialAnnuities.bSurvival N u N = u N := by
    unfold ActuarialAnnuities.bSurvival
    rw [Finset.sum_range_succ]
    have hzero :
        (∑ k ∈ Finset.range N, u k * ActuarialAnnuities.bAlive k N) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hnot : ¬ N ≤ k := Nat.not_le_of_gt (Finset.mem_range.mp hk)
      simp [ActuarialAnnuities.bAlive, hnot]
    rw [hzero]
    simp [ActuarialAnnuities.bAlive]
  have hfuture (N t : ℕ) (u : ℕ → ℝ) (ht : N < t) :
      ActuarialAnnuities.bSurvival N u t = 0 := by
    unfold ActuarialAnnuities.bSurvival
    apply Finset.sum_eq_zero
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hnot : ¬t ≤ k := by omega
    simp [ActuarialAnnuities.bAlive, hnot]
  have hage : ActuarialAnnuities.bUDDMicroSurvival h m p (a*m) =
      ActuarialAnnuities.bSurvival h p a := by
    by_cases ha : a < h
    · have hq : a*m < h*m := Nat.mul_lt_mul_of_pos_right ha hm
      rw [ActuarialAnnuities.micro_survival_udd h m (a*m) p hm hq]
      have hdiv : (a*m)/m=a := Nat.mul_div_cancel a hm
      have hrem : (a*m)%m=0 := by
        have heq := Nat.mod_add_div (a*m) m
        rw [hdiv, mul_comm m a] at heq
        omega
      simp [hdiv, hrem, ActuarialAnnuities.bUDD]
    · by_cases heq : a=h
      · subst a
        unfold ActuarialAnnuities.bUDDMicroSurvival
        rw [hlast (h*m) (ActuarialAnnuities.bUDDMicroMass h m p),
          hlast h p]
        simp [ActuarialAnnuities.bUDDMicroMass]
      · have hgt : h<a := by omega
        have hmgt : h*m<a*m := Nat.mul_lt_mul_of_pos_right hgt hm
        unfold ActuarialAnnuities.bUDDMicroSurvival
        rw [hfuture (h*m) (a*m)
          (ActuarialAnnuities.bUDDMicroMass h m p) hmgt,
          hfuture h a p hgt]
  have hcast : (((a*m : ℕ) : ℝ)/(m : ℝ)) = (a : ℝ) := by
    push_cast
    field_simp [hm0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ActuarialAnnuities.path_expectation_reconciliation h a n g 0 v b p
  · exact ActuarialAnnuities.path_expectation_reconciliation h a n g 1 v b p
  · exact ActuarialAnnuities.fractional_random_expectation h a n g 0 m w b p
  · exact ActuarialAnnuitiesContinuous.bc_continuous_reconciliation
      (h*m) (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) (n : ℝ) (g : ℝ) rho rate hn hi
  · exact ActuarialAnnuitiesContinuous.bc_continuous_guarantee_partition
      (h*m) (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) (n : ℝ) (g : ℝ) rho rate hn hi
  · exact ActuarialAnnuitiesBridge.bridge_micro_survival h m (a*m) p hm
  · calc
      ActuarialAnnuitiesContinuous.bcSurvival (h*m)
        (ActuarialAnnuities.bUDDMicroMass h m p)
        (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ) =
        ActuarialAnnuitiesContinuous.bcSurvival (h*m)
        (ActuarialAnnuities.bUDDMicroMass h m p)
        (fun k => (k : ℝ)/(m : ℝ))
          (((a*m : ℕ) : ℝ)/(m : ℝ)) := by rw [hcast]
      _ = ActuarialAnnuities.bUDDMicroSurvival h m p (a*m) :=
        ActuarialAnnuitiesBridge.bridge_micro_survival h m (a*m) p hm
      _ = ActuarialAnnuities.bSurvival h p a := hage
  · exact ActuarialAnnuities.udd_due_trapezoid_exact h m p hm
  · exact ActuarialAnnuitiesBridge.udd_micro_continuous_equals_arrears h m p hm
