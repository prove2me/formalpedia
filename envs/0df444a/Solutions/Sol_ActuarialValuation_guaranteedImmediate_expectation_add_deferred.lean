-- Prove2me | solution 1 for ActuarialValuation.guaranteedImmediate_expectation_add_deferred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:46:20.498325+00:00
-- url     : https://prove2.me/submissions/39269f4a-8dd9-4dbc-978d-fc1593321ec1

import Mathlib
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
import Definitions.Def_actuarial_annuityCertainImmediatePV
import Theorems.Thm_ActuarialValuation_guaranteedImmediate_eq_certain_add_deferred
import Theorems.Thm_ActuarialValuation_guaranteedImmediate_integrable
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
    (∫ ω, guaranteedAnnuityImmediatePV K v n ω ∂P) =
      annuityCertainImmediatePV v n + ∫ ω, deferredAnnuityImmediatePV K v n ω ∂P := by
  have hguar : Integrable (guaranteedAnnuityImmediatePV K v n) P :=
    guaranteedImmediate_integrable P K hK v hv0 hv1 n
  have htail : Integrable (deferredAnnuityImmediatePV K v n) P := by
    have hsub : Integrable
        (fun ω => guaranteedAnnuityImmediatePV K v n ω - annuityCertainImmediatePV v n) P :=
      hguar.sub (integrable_const _)
    apply hsub.congr
    exact Filter.Eventually.of_forall (fun ω => by
      change guaranteedAnnuityImmediatePV K v n ω - annuityCertainImmediatePV v n =
        deferredAnnuityImmediatePV K v n ω
      rw [guaranteedImmediate_eq_certain_add_deferred K v n ω]
      ring)
  calc
    (∫ ω, guaranteedAnnuityImmediatePV K v n ω ∂P) =
      ∫ ω, annuityCertainImmediatePV v n + deferredAnnuityImmediatePV K v n ω ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (fun ω => guaranteedImmediate_eq_certain_add_deferred K v n ω)
    _ = annuityCertainImmediatePV v n + ∫ ω, deferredAnnuityImmediatePV K v n ω ∂P := by
        rw [integral_add (integrable_const _) htail]
        simp
