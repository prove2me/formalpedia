-- Prove2me | solution 1 for ActuarialValuation.annualFutureLoss_integral_one_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T08:17:40.62223+00:00
-- url     : https://prove2.me/submissions/977e1b54-5cb2-42e2-b98b-5c897d48b858

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualFutureLoss
import Definitions.Def_actuarial_annualSurvivalMass
import Theorems.Thm_ActuarialValuation_annualFutureLoss_integrable
import Theorems.Thm_ActuarialValuation_annualFutureLoss_one_step
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ)
    (hK : Measurable K) (v : ℝ) (n t : ℕ) (b π : ℝ)
    (ht : t < n) :
    (∫ ω, annualFutureLoss K v n t b π ω ∂P) +
      π * annualSurvivalMass P K t =
      v * (b * annualDeathMass P K t +
        ∫ ω, annualFutureLoss K v n (t + 1) b π ω ∂P) := by
  let S : Set Ω := {ω | t ≤ K ω}
  let D : Set Ω := {ω | K ω = t}
  have hS : MeasurableSet S := by
    change MeasurableSet (K ⁻¹' Set.Ici t)
    exact hK measurableSet_Ici
  have hD : MeasurableSet D := by
    change MeasurableSet (K ⁻¹' {t})
    exact hK (measurableSet_singleton t)
  have hL : Integrable (annualFutureLoss K v n t b π) P :=
    annualFutureLoss_integrable P K hK v n t b π
  have hNext : Integrable (annualFutureLoss K v n (t + 1) b π) P :=
    annualFutureLoss_integrable P K hK v n (t + 1) b π
  have hPay : Integrable (fun ω : Ω => if t ≤ K ω then π else 0) P := by
    have hc : Integrable (fun _ : Ω => π) P := integrable_const _
    have hf : (fun ω : Ω => if t ≤ K ω then π else 0) =
        S.indicator (fun _ : Ω => π) := by
      funext ω
      by_cases h : t ≤ K ω <;> simp [S, Set.indicator, h]
    rw [hf]
    exact hc.indicator hS
  have hDeath : Integrable (fun ω : Ω => if K ω = t then v * b else 0) P := by
    have hc : Integrable (fun _ : Ω => v * b) P := integrable_const _
    have hf : (fun ω : Ω => if K ω = t then v * b else 0) =
        D.indicator (fun _ : Ω => v * b) := by
      funext ω
      by_cases h : K ω = t <;> simp [D, Set.indicator, h]
    rw [hf]
    exact hc.indicator hD
  have hPayIntegral :
      (∫ ω, (if t ≤ K ω then π else (0 : ℝ)) ∂P) =
        π * annualSurvivalMass P K t := by
    have hf : (fun ω : Ω => if t ≤ K ω then π else 0) =
        S.indicator (fun _ : Ω => π) := by
      funext ω
      by_cases h : t ≤ K ω <;> simp [S, Set.indicator, h]
    rw [show (∫ ω, (if t ≤ K ω then π else (0 : ℝ)) ∂P) =
        (∫ ω, S.indicator (fun _ : Ω => π) ω ∂P) from
          congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂P) hf]
    rw [integral_indicator_const π hS]
    change (P S).toReal * π = π * (P S).toReal
    ring
  have hDeathIntegral :
      (∫ ω, (if K ω = t then v * b else (0 : ℝ)) ∂P) =
        v * b * annualDeathMass P K t := by
    have hf : (fun ω : Ω => if K ω = t then v * b else 0) =
        D.indicator (fun _ : Ω => v * b) := by
      funext ω
      by_cases h : K ω = t <;> simp [D, Set.indicator, h]
    rw [show (∫ ω, (if K ω = t then v * b else (0 : ℝ)) ∂P) =
        (∫ ω, D.indicator (fun _ : Ω => v * b) ω ∂P) from
          congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂P) hf]
    rw [integral_indicator_const (v * b) hD]
    change (P D).toReal * (v * b) = (v * b) * (P D).toReal
    ring
  calc
    (∫ ω, annualFutureLoss K v n t b π ω ∂P) +
        π * annualSurvivalMass P K t =
        (∫ ω, annualFutureLoss K v n t b π ω ∂P) +
          (∫ ω, if t ≤ K ω then π else 0 ∂P) := by rw [hPayIntegral]
    _ = ∫ ω, (annualFutureLoss K v n t b π ω +
          (if t ≤ K ω then π else 0)) ∂P := by
          rw [integral_add hL hPay]
    _ = ∫ ω, ((if K ω = t then v * b else 0) +
          v * annualFutureLoss K v n (t + 1) b π ω) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact annualFutureLoss_one_step K v n t b π ω ht
    _ = (∫ ω, (if K ω = t then v * b else 0) ∂P) +
          v * (∫ ω, annualFutureLoss K v n (t + 1) b π ω ∂P) := by
          rw [integral_add hDeath (hNext.const_mul v), integral_const_mul]
    _ = v * (b * annualDeathMass P K t +
          ∫ ω, annualFutureLoss K v n (t + 1) b π ω ∂P) := by
          rw [hDeathIntegral]
          ring
