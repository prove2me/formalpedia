-- Prove2me | solution 1 for ActuarialValuation.deferredImmediate_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:04:29.17163+00:00
-- url     : https://prove2.me/submissions/96059125-dca7-4060-b1ed-d92632f14d9c

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deferredAnnuityImmediatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) =
      ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0 := by
  classical
  let F : ℕ → Ω → ℝ := fun k ω =>
    if n ≤ k then v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator
      (fun _ : Ω => (1 : ℝ)) ω else 0
  have hset (k : ℕ) : MeasurableSet (curtateSurvivalEvent K (k + 1)) := by
    change MeasurableSet {ω | k + 1 ≤ K ω}
    exact measurableSet_Ici.preimage hK
  have hint (k : ℕ) : Integrable (F k) P := by
    by_cases hn : n ≤ k
    · have hi : Integrable
          ((curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ))) P :=
        by
          have hc : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const (1 : ℝ)
          exact hc.indicator (hset k)
      simpa only [F, if_pos hn] using hi.const_mul (v ^ (k + 1))
    · simp [F, hn]
  have hnonneg (k : ℕ) (ω : Ω) : 0 ≤ F k ω := by
    by_cases hn : n ≤ k
    · by_cases hk : ω ∈ curtateSurvivalEvent K (k + 1)
      · simp [F, hn, Set.indicator, hk, pow_nonneg hv0 (k + 1)]
      · simp [F, hn, Set.indicator, hk]
    · simp [F, hn]
  have hnorm (k : ℕ) (ω : Ω) : ‖F k ω‖ = F k ω := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg k ω)]
  have heval (k : ℕ) :
      (∫ ω, F k ω ∂P) =
        if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0 := by
    by_cases hn : n ≤ k
    · simp only [F, if_pos hn]
      rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hset k)]
      simp [Measure.real]
    · simp [F, hn]
  have hnormeval (k : ℕ) :
      (∫ ω, ‖F k ω‖ ∂P) =
        if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0 := by
    calc
      _ = ∫ ω, F k ω ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hnorm k ω
      _ = _ := heval k
  have hprob (k : ℕ) : (P (curtateSurvivalEvent K (k + 1))).toReal ≤ 1 := by
    calc
      _ ≤ (P Set.univ).toReal :=
        ENNReal.toReal_mono (by simp) (measure_mono (Set.subset_univ _))
      _ = 1 := by simp
  have hsummable :
      Summable (fun k : ℕ => ∫ ω, ‖F k ω‖ ∂P) := by
    apply Summable.of_nonneg_of_le
      (fun k => by
        rw [hnormeval]
        split_ifs
        · exact mul_nonneg (pow_nonneg hv0 (k + 1)) ENNReal.toReal_nonneg
        · exact le_refl 0)
      (fun k => by
        rw [hnormeval]
        split_ifs
        · have hpow : v ^ (k + 1) ≤ v ^ k := by
            have hh : 0 ≤ v ^ k * (1 - v) :=
              mul_nonneg (pow_nonneg hv0 k) (sub_nonneg.mpr (le_of_lt hv1))
            rw [pow_succ]
            nlinarith
          calc
            v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal ≤ v ^ (k + 1) * 1 :=
              mul_le_mul_of_nonneg_left (hprob k) (pow_nonneg hv0 (k + 1))
            _ = v ^ (k + 1) := by ring
            _ ≤ v ^ k := hpow
        · exact pow_nonneg hv0 k)
      (summable_geometric_of_lt_one hv0 hv1)
  have hpoint (ω : Ω) :
      deferredAnnuityImmediatePV K v n ω = ∑' k : ℕ, F k ω := by
    have hzero : ∀ k ∉ Finset.range (K ω), F k ω = 0 := by
      intro k hk
      have hnot : ω ∉ curtateSurvivalEvent K (k + 1) := by
        change ¬ k + 1 ≤ K ω
        have hs : ¬ k < K ω := by simpa only [Finset.mem_range] using hk
        omega
      simp [F, Set.indicator, hnot]
    rw [tsum_eq_sum hzero]
    unfold deferredAnnuityImmediatePV
    apply Finset.sum_congr rfl
    intro k hk
    have hmem : ω ∈ curtateSurvivalEvent K (k + 1) := by
      change k + 1 ≤ K ω
      have hlt : k < K ω := Finset.mem_range.mp hk
      omega
    simp [F, Set.indicator, hmem]
  calc
    (∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) =
        ∫ ω, ∑' k : ℕ, F k ω ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact hpoint ω
    _ = ∑' k : ℕ, ∫ ω, F k ω ∂P :=
      (integral_tsum_of_summable_integral_norm hint hsummable).symm
    _ = ∑' k : ℕ, if n ≤ k then
        v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0 :=
      tsum_congr heval