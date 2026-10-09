-- Prove2me | solution 1 for ActuarialValuation.deferredImmediate_expectation_eq_whole_sub_temporary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:04:39.376554+00:00
-- url     : https://prove2.me/submissions/860df177-7ce0-4abe-87e9-f945172c7f38

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
import Theorems.Thm_ActuarialValuation_wholeLifeImmediate_integrable
import Theorems.Thm_ActuarialValuation_deferredImmediate_eq_whole_minus_temporary

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
      (∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) -
      (∑ k ∈ Finset.range n, v ^ (k + 1) *
        (P (curtateSurvivalEvent K (k + 1))).toReal) := by
  classical
  let F : ℕ → Ω → ℝ := fun k ω =>
    v ^ (k + 1) *
      (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω
  have hset (k : ℕ) : MeasurableSet (curtateSurvivalEvent K (k + 1)) := by
    change MeasurableSet {ω | (k + 1) ≤ K ω}
    exact measurableSet_Ici.preimage hK
  have hi (k : ℕ) : Integrable (F k) P := by
    have hc : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const (1 : ℝ)
    exact (hc.indicator (hset k)).const_mul (v ^ (k + 1))
  have hpref : Integrable (fun ω => ∑ k ∈ Finset.range n, F k ω) P :=
    integrable_finset_sum (Finset.range n) (fun k hk => hi k)
  have hwhole : Integrable (wholeLifeAnnuityImmediatePV K v) P :=
    wholeLifeImmediate_integrable P K hK v hv0 hv1
  have hval (k : ℕ) :
      (∫ ω, F k ω ∂P) =
        v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal := by
    change (∫ ω, v ^ (k + 1) *
      (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) = _
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hset k)]
    simp [Measure.real]
  calc
    (∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) =
        ∫ ω, wholeLifeAnnuityImmediatePV K v ω - ∑ k ∈ Finset.range n, F k ω ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact deferredImmediate_eq_whole_minus_temporary K v n ω
    _ = (∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) -
        (∫ ω, ∑ k ∈ Finset.range n, F k ω ∂P) :=
      integral_sub hwhole hpref
    _ = (∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) -
        (∑ k ∈ Finset.range n, ∫ ω, F k ω ∂P) := by
          rw [integral_finset_sum (Finset.range n) (fun k hk => hi k)]
    _ = (∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) -
        (∑ k ∈ Finset.range n, v ^ (k + 1) *
          (P (curtateSurvivalEvent K (k + 1))).toReal) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          exact hval k