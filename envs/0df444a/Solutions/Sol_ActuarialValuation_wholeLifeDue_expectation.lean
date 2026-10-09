-- Prove2me | solution 1 for ActuarialValuation.wholeLifeDue_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:04:14.218368+00:00
-- url     : https://prove2.me/submissions/f9c6f136-a1ed-4b26-b77d-c7ee28497f4b

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    :
    (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) =
      ∑' k : ℕ, v ^ k * (P (curtateSurvivalEvent K k)).toReal := by
  classical
  let F : ℕ → Ω → ℝ := fun k ω =>
    v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω
  have hset (k : ℕ) : MeasurableSet (curtateSurvivalEvent K k) := by
    change MeasurableSet {ω | k ≤ K ω}
    exact measurableSet_Ici.preimage hK
  have hint (k : ℕ) : Integrable (F k) P := by
    have hi : Integrable
        ((curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ))) P :=
      by
        have hc : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const (1 : ℝ)
        exact hc.indicator (hset k)
    exact hi.const_mul (v ^ k)
  have hnonneg (k : ℕ) (ω : Ω) : 0 ≤ F k ω := by
    by_cases hk : ω ∈ curtateSurvivalEvent K k
    · simp [F, Set.indicator, hk, pow_nonneg hv0 k]
    · simp [F, Set.indicator, hk]
  have hnorm (k : ℕ) (ω : Ω) : ‖F k ω‖ = F k ω := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg k ω)]
  have heval (k : ℕ) :
      (∫ ω, F k ω ∂P) =
        v ^ k * (P (curtateSurvivalEvent K k)).toReal := by
    change (∫ ω, v ^ k *
      (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) = _
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hset k)]
    simp [Measure.real]
  have hnormeval (k : ℕ) :
      (∫ ω, ‖F k ω‖ ∂P) =
        v ^ k * (P (curtateSurvivalEvent K k)).toReal := by
    calc
      _ = ∫ ω, F k ω ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hnorm k ω
      _ = _ := heval k
  have hprob (k : ℕ) : (P (curtateSurvivalEvent K k)).toReal ≤ 1 := by
    calc
      _ ≤ (P Set.univ).toReal :=
        ENNReal.toReal_mono (by simp) (measure_mono (Set.subset_univ _))
      _ = 1 := by simp
  have hsummable :
      Summable (fun k : ℕ => ∫ ω, ‖F k ω‖ ∂P) := by
    apply Summable.of_nonneg_of_le
      (fun k => by rw [hnormeval]; exact mul_nonneg (pow_nonneg hv0 k) ENNReal.toReal_nonneg)
      (fun k => by
        rw [hnormeval]
        calc
          v ^ k * (P (curtateSurvivalEvent K k)).toReal ≤ v ^ k * 1 :=
            mul_le_mul_of_nonneg_left (hprob k) (pow_nonneg hv0 k)
          _ = v ^ k := by ring)
      (summable_geometric_of_lt_one hv0 hv1)
  have hpoint (ω : Ω) :
      wholeLifeAnnuityDuePV K v ω = ∑' k : ℕ, F k ω := by
    have hzero : ∀ k ∉ Finset.range (K ω + 1), F k ω = 0 := by
      intro k hk
      have hnot : ω ∉ curtateSurvivalEvent K k := by
        change ¬ k ≤ K ω
        have hs : ¬ k < K ω + 1 := by simpa only [Finset.mem_range] using hk
        omega
      simp [F, Set.indicator, hnot]
    rw [tsum_eq_sum hzero]
    unfold wholeLifeAnnuityDuePV
    apply Finset.sum_congr rfl
    intro k hk
    have hmem : ω ∈ curtateSurvivalEvent K k := by
      change k ≤ K ω
      have hlt : k < K ω + 1 := Finset.mem_range.mp hk
      omega
    simp [F, Set.indicator, hmem]
  calc
    (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) =
        ∫ ω, ∑' k : ℕ, F k ω ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact hpoint ω
    _ = ∑' k : ℕ, ∫ ω, F k ω ∂P :=
      (integral_tsum_of_summable_integral_norm hint hsummable).symm
    _ = ∑' k : ℕ, v ^ k * (P (curtateSurvivalEvent K k)).toReal :=
      tsum_congr heval