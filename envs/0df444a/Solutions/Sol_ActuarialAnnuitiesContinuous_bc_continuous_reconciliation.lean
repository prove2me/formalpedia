-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_continuous_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T07:02:50.794166+00:00
-- url     : https://prove2.me/submissions/35905dcb-9182-492d-91a0-d121ccba3c4c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_actuarial_bcExpectedPV
import Definitions.Def_actuarial_bcProjectedPV

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
    bcExpectedPV N p life a term g rho b =
      bcProjectedPV N p life a term g rho b := by
  classical
  let B : ℝ → ℝ := fun t => b t * Real.exp (-rho*t)
  let Q : ℕ → ℝ → ℝ := fun k t =>
    B t * bcEntitled a g t (life k) * p k
  let G : ℕ → ℝ → ℝ := fun k t =>
    if t < a+g then B t*(bcAlive (life k) a*p k) else 0
  let P : ℕ → ℝ → ℝ := fun k t =>
    if a+g ≤ t then
      if t ≤ life k then B t*p k else 0
    else 0
  have hab : a ≤ a+term := by linarith
  have hB : IntegrableOn B (Set.Ioc a (a+term)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  have hG (k : ℕ) :
      IntegrableOn (G k) (Set.Ioc a (a+term)) volume := by
    have hb0 : IntegrableOn (fun t => B t*(bcAlive (life k) a*p k))
        (Set.Ioc a (a+term)) volume :=
      hB.mul_const (bcAlive (life k) a*p k)
    have hi := hb0.indicator
      (measurableSet_Iio : MeasurableSet (Set.Iio (a+g)))
    have heq : G k = (Set.Iio (a+g)).indicator
        (fun t => B t*(bcAlive (life k) a*p k)) := by
      funext t
      simp [G, Set.indicator, Set.mem_Iio]
    rw [heq]
    exact hi
  have hP (k : ℕ) :
      IntegrableOn (P k) (Set.Ioc a (a+term)) volume := by
    have hb0 : IntegrableOn (fun t => B t*p k)
        (Set.Ioc a (a+term)) volume := hB.mul_const (p k)
    have hi := hb0.indicator
      (measurableSet_Iic : MeasurableSet (Set.Iic (life k)))
    have hj := hi.indicator
      (measurableSet_Ici : MeasurableSet (Set.Ici (a+g)))
    have heq : P k = (Set.Ici (a+g)).indicator
        ((Set.Iic (life k)).indicator (fun t => B t*p k)) := by
      funext t
      by_cases hc : a+g ≤ t
      · by_cases hl : t ≤ life k
        · simp [P, Set.indicator, hc, hl]
        · simp [P, Set.indicator, hc, hl]
      · simp [P, Set.indicator, hc]
    rw [heq]
    exact hj
  have hQeq (k : ℕ) : Q k = fun t => G k t+P k t := by
    funext t
    by_cases hc : t < a+g
    · have hnle : ¬a+g ≤ t := not_le.mpr hc
      simp [Q, G, P, bcEntitled, hc, hnle, mul_comm, mul_left_comm, mul_assoc]
    · have hle : a+g ≤ t := le_of_not_gt hc
      by_cases hl : t ≤ life k
      · simp [Q, G, P, bcEntitled, bcAlive, hc, hle, hl, mul_comm, mul_left_comm, mul_assoc]
      · simp [Q, G, P, bcEntitled, bcAlive, hc, hle, hl]
  have hQ (k : ℕ) : IntervalIntegrable (Q k) volume a (a+term) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    rw [hQeq]
    exact (hG k).add (hP k)
  have hpath (k : ℕ) :
      p k * bcPathPV a term g rho b (life k) =
        ∫ t in a..(a+term), Q k t := by
    unfold bcPathPV
    change p k * (∫ t in a..(a+term),
      B t * bcEntitled a g t (life k)) =
        ∫ t in a..(a+term),
          (B t * bcEntitled a g t (life k))*p k
    rw [intervalIntegral.integral_mul_const]
    ring
  have hpoint (t : ℝ) :
      (∑ k ∈ Finset.range (N+1), Q k t) =
       B t*(if t<a+g then bcSurvival N p life a else
         bcSurvival N p life t) := by
    by_cases hc : t < a+g
    · simp only [if_pos hc]
      unfold bcSurvival
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp [Q, bcEntitled, hc, mul_comm, mul_left_comm, mul_assoc]
    · simp only [if_neg hc]
      unfold bcSurvival
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp [Q, bcEntitled, hc, mul_comm, mul_left_comm, mul_assoc]
  have hswap :
      (∫ t in a..(a+term), ∑ k ∈ Finset.range (N+1), Q k t) =
       ∑ k ∈ Finset.range (N+1),
         ∫ t in a..(a+term), Q k t :=
    intervalIntegral.integral_finset_sum (fun k hk => hQ k)
  calc
    bcExpectedPV N p life a term g rho b =
        ∑ k ∈ Finset.range (N+1),
          ∫ t in a..(a+term), Q k t := by
      unfold bcExpectedPV
      apply Finset.sum_congr rfl
      intro k hk
      exact hpath k
    _ = ∫ t in a..(a+term), ∑ k ∈ Finset.range (N+1), Q k t :=
      hswap.symm
    _ = bcProjectedPV N p life a term g rho b := by
      unfold bcProjectedPV
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t
