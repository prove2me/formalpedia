-- Prove2me | solution 1 for ActuarialValuation.guaranteedDue_expectation_survival_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:09:26.550977+00:00
-- url     : https://prove2.me/submissions/2452e97a-e677-4d46-a32e-2586bd6fb73f

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_annuityCertainDuePV
import Theorems.Thm_ActuarialValuation_deferredDue_eq_survival_tsum
import Theorems.Thm_ActuarialValuation_guaranteedDue_expectation_add_deferred
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
    (∫ ω, guaranteedAnnuityDuePV K v n ω ∂P) =
      annuityCertainDuePV v n +
      ∑' k : ℕ, if n ≤ k then v ^ k *
        (P (curtateSurvivalEvent K k)).toReal else 0 := by
  classical
  let F : ℕ → Ω → ℝ := fun k ω =>
    if n ≤ k then v ^ k * (curtateSurvivalEvent K k).indicator
      (fun _ : Ω => (1 : ℝ)) ω else 0
  have hset (k : ℕ) : MeasurableSet (curtateSurvivalEvent K k) := by
    change MeasurableSet {ω | k ≤ K ω}
    exact measurableSet_Ici.preimage hK
  have hint (k : ℕ) : Integrable (F k) P := by
    by_cases hn : n ≤ k
    · have hconst : Integrable (fun _ : Ω => (1 : ℝ)) P :=
        integrable_const _
      have hi : Integrable
          ((curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ))) P :=
        hconst.indicator (hset k)
      simpa only [F, if_pos hn] using hi.const_mul (v ^ k)
    · simp [F, hn]
  have hnonneg (k : ℕ) (ω : Ω) : 0 ≤ F k ω := by
    by_cases hn : n ≤ k
    · by_cases hk : ω ∈ curtateSurvivalEvent K k
      · simp [F, hn, Set.indicator, hk, pow_nonneg hv0 k]
      · simp [F, hn, Set.indicator, hk]
    · simp [F, hn]
  have hnorm (k : ℕ) (ω : Ω) : ‖F k ω‖ = F k ω := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg k ω)]
  have heval (k : ℕ) :
      (∫ ω, F k ω ∂P) =
        if n ≤ k then v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0 := by
    by_cases hn : n ≤ k
    · simp only [F, if_pos hn]
      rw [integral_const_mul]
      exact congrArg (fun t : ℝ => v ^ k * t)
        (integral_indicator_one (μ := P) (hset k))
    · simp [F, hn]
  have hnormeval (k : ℕ) :
      (∫ ω, ‖F k ω‖ ∂P) =
        if n ≤ k then v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0 := by
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
      (fun k => by
        rw [hnormeval]
        split_ifs
        · exact mul_nonneg (pow_nonneg hv0 k) ENNReal.toReal_nonneg
        · exact le_refl 0)
      (fun k => by
        rw [hnormeval]
        split_ifs
        · calc
            v ^ k * (P (curtateSurvivalEvent K k)).toReal ≤ v ^ k * 1 :=
              mul_le_mul_of_nonneg_left (hprob k) (pow_nonneg hv0 k)
            _ = v ^ k := by ring
        · exact pow_nonneg hv0 k)
      (summable_geometric_of_lt_one hv0 hv1)
  have hpoint (ω : Ω) :
      deferredAnnuityDuePV K v n ω = ∑' k : ℕ, F k ω := by
    exact deferredDue_eq_survival_tsum K v n ω
  have hdeferred :
    (∫ ω, deferredAnnuityDuePV K v n ω ∂P) =
      ∑' k : ℕ, if n ≤ k then v ^ k *
        (P (curtateSurvivalEvent K k)).toReal else 0 := by
    calc
      (∫ ω, deferredAnnuityDuePV K v n ω ∂P) =
          ∫ ω, ∑' k : ℕ, F k ω ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact hpoint ω
      _ = ∑' k : ℕ, ∫ ω, F k ω ∂P :=
        (integral_tsum_of_summable_integral_norm hint hsummable).symm
      _ = ∑' k : ℕ, if n ≤ k then
          v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0 :=
        tsum_congr heval
  calc
    (∫ ω, guaranteedAnnuityDuePV K v n ω ∂P) =
        annuityCertainDuePV v n + (∫ ω, deferredAnnuityDuePV K v n ω ∂P) :=
      guaranteedDue_expectation_add_deferred P K hK v hv0 hv1 n
    _ = annuityCertainDuePV v n +
      ∑' k : ℕ, if n ≤ k then v ^ k *
        (P (curtateSurvivalEvent K k)).toReal else 0 := by
      rw [hdeferred]
