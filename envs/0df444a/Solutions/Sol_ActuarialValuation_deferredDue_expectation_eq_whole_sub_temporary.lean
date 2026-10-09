-- Prove2me | solution 1 for ActuarialValuation.deferredDue_expectation_eq_whole_sub_temporary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:17:55.312192+00:00
-- url     : https://prove2.me/submissions/b8b01a04-f805-47b6-be58-21d9ab1ff6ea

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Theorems.Thm_ActuarialValuation_wholeLifeDue_integrable
import Theorems.Thm_ActuarialValuation_deferredDue_eq_whole_minus_temporary

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
    (∫ ω, deferredAnnuityDuePV K v n ω ∂P) =
      (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) -
      (∑ k ∈ Finset.range n, v ^ k *
        (P (curtateSurvivalEvent K k)).toReal) := by
  classical
  let F : ℕ → Ω → ℝ := fun k ω =>
    v ^ k *
      (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω
  have hset (k : ℕ) : MeasurableSet (curtateSurvivalEvent K k) := by
    change MeasurableSet {ω | k ≤ K ω}
    exact measurableSet_Ici.preimage hK
  have hi (k : ℕ) : Integrable (F k) P := by
    have hc : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const (1 : ℝ)
    exact (hc.indicator (hset k)).const_mul (v ^ k)
  have hpref : Integrable (fun ω => ∑ k ∈ Finset.range n, F k ω) P :=
    integrable_finset_sum (Finset.range n) (fun k hk => hi k)
  have hwhole : Integrable (wholeLifeAnnuityDuePV K v) P :=
    wholeLifeDue_integrable P K hK v hv0 hv1
  have hval (k : ℕ) :
      (∫ ω, F k ω ∂P) =
        v ^ k * (P (curtateSurvivalEvent K k)).toReal := by
    change (∫ ω, v ^ k *
      (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) = _
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hset k)]
    simp [Measure.real]
  calc
    (∫ ω, deferredAnnuityDuePV K v n ω ∂P) =
        ∫ ω, wholeLifeAnnuityDuePV K v ω - ∑ k ∈ Finset.range n, F k ω ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact deferredDue_eq_whole_minus_temporary K v n ω
    _ = (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) -
        (∫ ω, ∑ k ∈ Finset.range n, F k ω ∂P) :=
      integral_sub hwhole hpref
    _ = (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) -
        (∑ k ∈ Finset.range n, ∫ ω, F k ω ∂P) := by
          rw [integral_finset_sum (Finset.range n) (fun k hk => hi k)]
    _ = (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) -
        (∑ k ∈ Finset.range n, v ^ k *
          (P (curtateSurvivalEvent K k)).toReal) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          exact hval k