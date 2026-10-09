-- Prove2me | solution 1 for ActuarialValuation.guaranteedDue_expectation_add_deferred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:46:09.981334+00:00
-- url     : https://prove2.me/submissions/d4c55c52-d542-4e54-a562-c0053f1f3479

import Mathlib
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_annuityCertainDuePV
import Theorems.Thm_ActuarialValuation_guaranteedDue_eq_certain_add_deferred
import Theorems.Thm_ActuarialValuation_guaranteedDue_integrable
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
      annuityCertainDuePV v n + ∫ ω, deferredAnnuityDuePV K v n ω ∂P := by
  have hguar : Integrable (guaranteedAnnuityDuePV K v n) P :=
    guaranteedDue_integrable P K hK v hv0 hv1 n
  have htail : Integrable (deferredAnnuityDuePV K v n) P := by
    have hsub : Integrable
        (fun ω => guaranteedAnnuityDuePV K v n ω - annuityCertainDuePV v n) P :=
      hguar.sub (integrable_const _)
    apply hsub.congr
    exact Filter.Eventually.of_forall (fun ω => by
      change guaranteedAnnuityDuePV K v n ω - annuityCertainDuePV v n =
        deferredAnnuityDuePV K v n ω
      rw [guaranteedDue_eq_certain_add_deferred K v n ω]
      ring)
  calc
    (∫ ω, guaranteedAnnuityDuePV K v n ω ∂P) =
      ∫ ω, annuityCertainDuePV v n + deferredAnnuityDuePV K v n ω ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (fun ω => guaranteedDue_eq_certain_add_deferred K v n ω)
    _ = annuityCertainDuePV v n + ∫ ω, deferredAnnuityDuePV K v n ω ∂P := by
        rw [integral_add (integrable_const _) htail]
        simp
