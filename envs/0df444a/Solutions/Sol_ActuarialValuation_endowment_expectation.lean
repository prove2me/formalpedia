-- Prove2me | solution 1 for ActuarialValuation.endowment_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:21:25.248149+00:00
-- url     : https://prove2.me/submissions/127f34fd-e4ee-472d-b47b-ab034a3d4c7c

import Mathlib
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_curtatePureEndowmentPV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deathYearEvent
import Theorems.Thm_ActuarialValuation_termAssurance_expectation
import Theorems.Thm_ActuarialValuation_presentValue_integrable
import Theorems.Thm_ActuarialValuation_singlePayment_expectation
import Theorems.Thm_ActuarialValuation_termAssurancePV_eq_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    : (∫ ω, endowmentAssurancePV K v n ω ∂P) = (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) + v ^ n * (P (curtateSurvivalEvent K n)).toReal := by
  classical
  have hdecomp (ω : Ω) : endowmentAssurancePV K v n ω =
      termAssurancePV K v n ω + curtatePureEndowmentPV K v n ω := by
    classical
    have hsum :
        termAssurancePV K v n ω =
          ∑ k ∈ Finset.range n, if K ω = k then v ^ (k + 1) else 0 := by
      rw [termAssurancePV_eq_sum K v n ω]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases heq : K ω = k
      · simp [deathYearEvent, Set.indicator, heq]
      · simp [deathYearEvent, Set.indicator, heq]
    rw [hsum]
    by_cases hlt : K ω < n
    · have hle : K ω + 1 ≤ n := Nat.succ_le_iff.mpr hlt
      have hpay :
          (∑ k ∈ Finset.range n, if K ω = k then v ^ (k + 1) else 0) =
            v ^ (K ω + 1) := by
        rw [Finset.sum_eq_single (K ω)]
        · simp [Finset.mem_range.mpr hlt]
        · intro j hj hneq
          simp [hneq.symm]
        · intro hnot
          exact False.elim (hnot (Finset.mem_range.mpr hlt))
      have hmin : min (K ω + 1) n = K ω + 1 := min_eq_left hle
      have hnosurv : ¬ n ≤ K ω := Nat.not_le_of_gt hlt
      simp [endowmentAssurancePV, hmin, curtatePureEndowmentPV,
            curtateSurvivalEvent, Set.indicator, hnosurv, hpay]
    · have hsurv : n ≤ K ω := Nat.le_of_not_gt hlt
      have hpay :
          (∑ k ∈ Finset.range n, if K ω = k then v ^ (k + 1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        have hneq : K ω ≠ k := by omega
        simp [hneq]
      have hmin : min (K ω + 1) n = n := min_eq_right (by omega)
      simp [endowmentAssurancePV, hmin, curtatePureEndowmentPV,
            curtateSurvivalEvent, Set.indicator, hsurv, hpay]
  have hA : MeasurableSet (curtateSurvivalEvent K n) := by
    change MeasurableSet (K ⁻¹' Set.Ici n)
    exact hK measurableSet_Ici
  have hdeath (k : ℕ) : MeasurableSet (deathYearEvent K k) := by
    change MeasurableSet (K ⁻¹' {k})
    exact hK (measurableSet_singleton k)
  have hterm : Integrable (termAssurancePV K v n) P := by
    unfold termAssurancePV
    exact presentValue_integrable P (Finset.range n) (fun k : ℕ => k + 1)
      (fun t : ℕ => v ^ t) (fun _ : ℕ => (1 : ℝ))
      (deathYearEvent K) (by intro k hk; exact hdeath k)
  have hmat : Integrable (curtatePureEndowmentPV K v n) P := by
    have heq : curtatePureEndowmentPV K v n =
        (curtateSurvivalEvent K n).indicator (fun _ : Ω => v ^ n) := by
      funext ω
      by_cases hw : ω ∈ curtateSurvivalEvent K n <;>
        simp [curtatePureEndowmentPV, Set.indicator, hw]
    rw [heq]
    exact (integrable_const (v ^ n)).indicator hA
  have hmaturity :
      (∫ ω, curtatePureEndowmentPV K v n ω ∂P) =
      v ^ n * (P (curtateSurvivalEvent K n)).toReal := by
    unfold curtatePureEndowmentPV
    simpa only [mul_one] using
      (singlePayment_expectation P (curtateSurvivalEvent K n) hA (v ^ n) (1 : ℝ))
  calc
    (∫ ω, endowmentAssurancePV K v n ω ∂P) =
        ∫ ω, (termAssurancePV K v n ω + curtatePureEndowmentPV K v n ω) ∂P := by
      congr 1
      funext ω
      exact hdecomp ω
    _ = (∫ ω, termAssurancePV K v n ω ∂P) +
        (∫ ω, curtatePureEndowmentPV K v n ω ∂P) :=
      integral_add hterm hmat
    _ = (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) +
        v ^ n * (P (curtateSurvivalEvent K n)).toReal := by
      rw [termAssurance_expectation P K hK v n, hmaturity]
