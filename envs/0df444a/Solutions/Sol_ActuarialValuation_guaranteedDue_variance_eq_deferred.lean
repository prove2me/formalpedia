-- Prove2me | solution 1 for ActuarialValuation.guaranteedDue_variance_eq_deferred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:55:51.675469+00:00
-- url     : https://prove2.me/submissions/f94ce272-0b52-494f-91e3-0b78281e12f6

import Mathlib
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_annuityCertainDuePV
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Theorems.Thm_ActuarialValuation_guaranteedDue_eq_certain_add_deferred
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
    ProbabilityTheory.variance (guaranteedAnnuityDuePV K v n) P =
      ProbabilityTheory.variance (deferredAnnuityDuePV K v n) P := by
  have hm : Measurable (deferredAnnuityDuePV K v n) := by
    have hdisc : Measurable (fun m : ℕ =>
        ∑ k ∈ Finset.range (m + 1),
          if n ≤ k then v ^ k else 0) := measurable_of_countable _
    change Measurable (fun ω : Ω =>
      ∑ k ∈ Finset.range (K ω + 1),
        if n ≤ k then v ^ k else 0)
    exact hdisc.comp hK
  have heq : guaranteedAnnuityDuePV K v n =
      (fun ω => annuityCertainDuePV v n + deferredAnnuityDuePV K v n ω) := by
    funext ω
    exact guaranteedDue_eq_certain_add_deferred K v n ω
  rw [heq]
  exact ProbabilityTheory.variance_const_add hm.aestronglyMeasurable
    (annuityCertainDuePV v n)
