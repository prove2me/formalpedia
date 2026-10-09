-- Prove2me | solution 1 for ActuarialValuation.guaranteedImmediate_variance_eq_deferred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:56:02.328395+00:00
-- url     : https://prove2.me/submissions/2a641ca6-4a56-4a3e-95df-af38e4c69a2d

import Mathlib
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
import Definitions.Def_actuarial_annuityCertainImmediatePV
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
import Theorems.Thm_ActuarialValuation_guaranteedImmediate_eq_certain_add_deferred
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
    ProbabilityTheory.variance (guaranteedAnnuityImmediatePV K v n) P =
      ProbabilityTheory.variance (deferredAnnuityImmediatePV K v n) P := by
  have hm : Measurable (deferredAnnuityImmediatePV K v n) := by
    have hdisc : Measurable (fun m : ℕ =>
        ∑ k ∈ Finset.range (m),
          if n ≤ k then v ^ (k + 1) else 0) := measurable_of_countable _
    change Measurable (fun ω : Ω =>
      ∑ k ∈ Finset.range (K ω),
        if n ≤ k then v ^ (k + 1) else 0)
    exact hdisc.comp hK
  have heq : guaranteedAnnuityImmediatePV K v n =
      (fun ω => annuityCertainImmediatePV v n + deferredAnnuityImmediatePV K v n ω) := by
    funext ω
    exact guaranteedImmediate_eq_certain_add_deferred K v n ω
  rw [heq]
  exact ProbabilityTheory.variance_const_add hm.aestronglyMeasurable
    (annuityCertainImmediatePV v n)
