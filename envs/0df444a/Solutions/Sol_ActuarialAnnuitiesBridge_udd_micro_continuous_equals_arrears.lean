-- Prove2me | solution 1 for ActuarialAnnuitiesBridge.udd_micro_continuous_equals_arrears
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T12:09:55.437623+00:00
-- url     : https://prove2.me/submissions/fceb9377-3c92-4372-bc1a-c80446228fd4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_bcExpectedPV
import Definitions.Def_actuarial_bcPathPV
import Definitions.Def_actuarial_bcEntitled
import Definitions.Def_actuarial_bcAlive
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bAlive
import Definitions.Def_actuarial_bUDDMicroMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
theorem solution (h m : ℕ) (p : ℕ → ℝ) (hm : 0 < m) :
    ActuarialAnnuitiesContinuous.bcExpectedPV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) 0 (h : ℝ) 0 0 (fun _ => 1) =
    ActuarialAnnuities.bFractionalSurvivalPV h 0 h 0 1 m 1
      (fun _ => 1) p := by
  classical
  let N := h*m
  let w := ActuarialAnnuities.bUDDMicroMass h m p
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hN (k:ℕ) (hk:k≤N) : (k:ℝ)/(m:ℝ) ∈ Set.Icc (0:ℝ) (h:ℝ) := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hmpos.le
    · have hkr : (k:ℝ) ≤ (h:ℝ)*(m:ℝ) := by
        exact_mod_cast hk
      exact (div_le_iff₀ hmpos).mpr hkr
  have hpath (k:ℕ) (hk:k≤N) :
      ActuarialAnnuitiesContinuous.bcPathPV 0 (h:ℝ) 0 0
        (fun _ => 1) ((k:ℝ)/(m:ℝ)) = (k:ℝ)/(m:ℝ) := by
    have hint : (∫ t in (0:ℝ)..(h:ℝ), (1:ℝ)*Real.exp (-0*t)*
          ActuarialAnnuitiesContinuous.bcEntitled 0 0 t ((k:ℝ)/(m:ℝ))) =
      (∫ t in (0:ℝ)..(h:ℝ), (Set.Iic ((k:ℝ)/(m:ℝ))).indicator (fun _ => (1:ℝ)) t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      by_cases ht0 : t < 0
      · have hle : t ≤ (k:ℝ)/(m:ℝ) := le_trans ht0.le (hN k hk).1
        simp [ActuarialAnnuitiesContinuous.bcEntitled,
          ActuarialAnnuitiesContinuous.bcAlive, Set.indicator, Set.mem_Iic,
          ht0, hle, (hN k hk).1]
      · simp [ActuarialAnnuitiesContinuous.bcEntitled,
          ActuarialAnnuitiesContinuous.bcAlive, Set.indicator, Set.mem_Iic, ht0]
    calc
      ActuarialAnnuitiesContinuous.bcPathPV 0 (h:ℝ) 0 0 (fun _ => 1)
          ((k:ℝ)/(m:ℝ)) = (∫ t in (0:ℝ)..(h:ℝ), (1:ℝ)*Real.exp (-0*t)*
          ActuarialAnnuitiesContinuous.bcEntitled 0 0 t ((k:ℝ)/(m:ℝ))) := by simp only [ActuarialAnnuitiesContinuous.bcPathPV, zero_add]
      _ = (∫ t in (0:ℝ)..(h:ℝ),
          (Set.Iic ((k:ℝ)/(m:ℝ))).indicator (fun _ => (1:ℝ)) t) := hint
      _ = (∫ t in (0:ℝ)..((k:ℝ)/(m:ℝ)), (1:ℝ)) :=
        intervalIntegral.integral_indicator (hN k hk)
      _ = (k:ℝ)/(m:ℝ) := by simp
  have hcont :
      ActuarialAnnuitiesContinuous.bcExpectedPV N w (fun k => (k:ℝ)/(m:ℝ))
        0 (h:ℝ) 0 0 (fun _=>1) = ∑ k ∈ Finset.range (N+1), w k*((k:ℝ)/(m:ℝ)) := by
    unfold ActuarialAnnuitiesContinuous.bcExpectedPV
    apply Finset.sum_congr rfl
    intro k hk
    rw [hpath k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  have hfrac :
      ActuarialAnnuities.bFractionalSurvivalPV h 0 h 0 1 m 1 (fun _=>1) p =
      ∑ q ∈ Finset.range N, (1/(m:ℝ))*ActuarialAnnuities.bSurvival N w (q+1) := by
    unfold ActuarialAnnuities.bFractionalSurvivalPV
      ActuarialAnnuities.bSurvivalPV
    apply Finset.sum_congr rfl
    intro q hq
    have hqn : q<N := Finset.mem_range.mp hq
    simp [N,w,hqn]
  have hcount (k:ℕ) (hk:k≤N) :
      (∑ q ∈ Finset.range N,
        if q<k then (1:ℝ) else 0) = (k:ℝ) := by
    have hh : N=k+(N-k) := (Nat.add_sub_of_le hk).symm
    have hhead : (∑ q∈Finset.range k,
        if q<k then (1:ℝ) else 0) = (k:ℝ) := by
      calc
        _ = ∑ q∈Finset.range k, (1:ℝ) := by
          apply Finset.sum_congr rfl
          intro q hq
          simp [Finset.mem_range.mp hq]
        _ = (k:ℝ) := by simp
    have htail : (∑ r∈Finset.range (N-k),
        if k+r<k then (1:ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hf : ¬ k+r<k := by omega
      simp [hf]
    calc
      (∑ q∈Finset.range N,
        if q<k then (1:ℝ) else 0) =
          (∑ q∈Finset.range k, if q<k then (1:ℝ) else 0) +
          (∑ r∈Finset.range (N-k),
            if k+r<k then (1:ℝ) else 0) := by
          conv_lhs => rw [hh, Finset.sum_range_add]
      _ = (k:ℝ) := by rw [hhead, htail, add_zero]
  have hweighted (k:ℕ) (hk:k≤N) :
      (∑ q∈Finset.range N,
        (1/(m:ℝ))*(w k*ActuarialAnnuities.bAlive k (q+1))) =
      w k*((k:ℝ)/(m:ℝ)) := by
    have ha (q:ℕ) : ActuarialAnnuities.bAlive k (q+1) =
        if q<k then (1:ℝ) else 0 := by
      unfold ActuarialAnnuities.bAlive
      by_cases hq:q<k
      · have hle:q+1≤k := by omega
        simp [hq, hle]
      · have hn:¬q+1≤k := by omega
        simp [hq, hn]
    calc
      (∑ q∈Finset.range N,
        (1/(m:ℝ))*(w k*ActuarialAnnuities.bAlive k (q+1))) =
        ((1/(m:ℝ))*w k)*
          (∑ q∈Finset.range N, if q<k then (1:ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [ha q]
          split_ifs <;> ring
      _ = w k*((k:ℝ)/(m:ℝ)) := by
        rw [hcount k hk]
        ring
  have hfracval :
      ActuarialAnnuities.bFractionalSurvivalPV h 0 h 0 1 m 1
        (fun _=>1) p =
      ∑ k∈Finset.range (N+1), w k*((k:ℝ)/(m:ℝ)) := by
    rw [hfrac]
    simp_rw [ActuarialAnnuities.bSurvival]
    calc
      (∑ q∈Finset.range N,
        (1/(m:ℝ))*(∑ k∈Finset.range (N+1),
          w k*ActuarialAnnuities.bAlive k (q+1))) =
        ∑ q∈Finset.range N, ∑ k∈Finset.range (N+1),
          (1/(m:ℝ))*(w k*ActuarialAnnuities.bAlive k (q+1)) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
      _ = ∑ k∈Finset.range (N+1), ∑ q∈Finset.range N,
          (1/(m:ℝ))*(w k*ActuarialAnnuities.bAlive k (q+1)) := by
          rw [Finset.sum_comm]
      _ = ∑ k∈Finset.range (N+1), w k*((k:ℝ)/(m:ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hweighted k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  exact hcont.trans hfracval.symm
