-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_continuous_guarantee_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T07:07:29.532182+00:00
-- url     : https://prove2.me/submissions/2e89b914-0a60-491e-9412-2d742fd802cf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bcProjectedPV
import Definitions.Def_actuarial_bcGuaranteedPV
import Definitions.Def_actuarial_bcPostGuaranteePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialAnnuitiesContinuous

theorem solution (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ)
    (a term g rho : ℝ) (b : ℝ → ℝ)
    (hn : 0 ≤ term)
    (hint : IntervalIntegrable (fun t => b t * Real.exp (-rho*t))
      volume a (a+term)) :
    bcProjectedPV N p life a term g rho b =
      bcGuaranteedPV N p life a term g rho b +
        bcPostGuaranteePV N p life a term g rho b := by
  classical
  let B : ℝ → ℝ := fun t => b t * Real.exp (-rho*t)
  let S : ℝ → ℝ := fun t => bcSurvival N p life t
  let G : ℝ → ℝ := fun t =>
    if t < a+g then B t*S a else 0
  let P : ℝ → ℝ := fun t =>
    if a+g ≤ t then B t*S t else 0
  let K : ℕ → ℝ → ℝ := fun k t =>
    if a+g ≤ t then
      if t ≤ life k then B t*p k else 0
    else 0
  have hab : a ≤ a+term := by linarith
  have hB : IntegrableOn B (Set.Ioc a (a+term)) volume := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  have hG : IntegrableOn G (Set.Ioc a (a+term)) volume := by
    have hb0 : IntegrableOn (fun t => B t*S a)
        (Set.Ioc a (a+term)) volume := hB.mul_const (S a)
    have hi := hb0.indicator (measurableSet_Iio : MeasurableSet (Set.Iio (a+g)))
    have heq : G = (Set.Iio (a+g)).indicator (fun t => B t*S a) := by
      funext t
      simp [G, Set.indicator, Set.mem_Iio]
    rw [heq]
    exact hi
  have hK (k : ℕ) :
      IntegrableOn (K k) (Set.Ioc a (a+term)) volume := by
    have hb0 : IntegrableOn (fun t => B t*p k)
        (Set.Ioc a (a+term)) volume := hB.mul_const (p k)
    have hi := hb0.indicator
      (measurableSet_Iic : MeasurableSet (Set.Iic (life k)))
    have hj := hi.indicator
      (measurableSet_Ici : MeasurableSet (Set.Ici (a+g)))
    have heq : K k = (Set.Ici (a+g)).indicator
        ((Set.Iic (life k)).indicator (fun t => B t*p k)) := by
      funext t
      by_cases hc : a+g ≤ t
      · by_cases hl : t ≤ life k
        · simp [K, Set.indicator, hc, hl]
        · simp [K, Set.indicator, hc, hl]
      · simp [K, Set.indicator, hc]
    rw [heq]
    exact hj
  have hsum (s : Finset ℕ) :
      IntegrableOn (fun t => ∑ k ∈ s, K k t)
        (Set.Ioc a (a+term)) volume := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hnot ih =>
      have hadd : IntegrableOn
          ((K k) + (fun t => ∑ j ∈ s, K j t))
          (Set.Ioc a (a+term)) volume := (hK k).add ih
      have heq : (fun t => ∑ j ∈ insert k s, K j t) =
          ((K k) + (fun t => ∑ j ∈ s, K j t)) := by
        funext t
        simp [Finset.sum_insert hnot, Pi.add_apply]
      rw [heq]
      exact hadd
  have hPpoint (t : ℝ) :
      P t = ∑ k ∈ Finset.range (N+1), K k t := by
    by_cases hc : a+g ≤ t
    · simp only [P, K, if_pos hc]
      unfold S bcSurvival
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hl : t ≤ life k
      · simp [bcAlive, hl, mul_comm, mul_left_comm, mul_assoc]
      · simp [bcAlive, hl]
    · simp [P, K, hc]
  have hP : IntegrableOn P (Set.Ioc a (a+term)) volume := by
    have hfun : P = fun t => ∑ k ∈ Finset.range (N+1), K k t :=
      funext hPpoint
    rw [hfun]
    exact hsum _
  have hGi : IntervalIntegrable G volume a (a+term) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hG
  have hPi : IntervalIntegrable P volume a (a+term) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hP
  calc
    bcProjectedPV N p life a term g rho b =
        ∫ t in a..(a+term), G t+P t := by
      unfold bcProjectedPV
      apply intervalIntegral.integral_congr
      intro t ht
      by_cases hc : t < a+g
      · have hnle : ¬ a+g ≤ t := not_le.mpr hc
        simp [B, S, G, P, hc, hnle]
      · have hle : a+g ≤ t := le_of_not_gt hc
        simp [B, S, G, P, hc, hle]
    _ = (∫ t in a..(a+term), G t) +
        (∫ t in a..(a+term), P t) :=
          intervalIntegral.integral_add hGi hPi
    _ = bcGuaranteedPV N p life a term g rho b +
        bcPostGuaranteePV N p life a term g rho b := by
      rfl
