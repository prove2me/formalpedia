-- Prove2me | solution 1 for ActuarialValuation.annualReserve_one_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T08:31:41.399983+00:00
-- url     : https://prove2.me/submissions/06aab675-8cfb-465b-b310-8e36dd388d8c

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualProspectiveReserve
import Definitions.Def_actuarial_annualSurvivalMass
import Theorems.Thm_ActuarialValuation_annualReserve_mass_identity
import Theorems.Thm_ActuarialValuation_annualFutureLoss_integral_one_step
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ)
    (hK : Measurable K) (v : ℝ) (n t : ℕ) (b π : ℝ)
    (ht : t < n) (hS : 0 < annualSurvivalMass P K t)
    (hNext : 0 < annualSurvivalMass P K (t + 1)) :
    annualProspectiveReserve P K v n t b π + π =
      v * (annualDeathMass P K t / annualSurvivalMass P K t * b +
        annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t *
          annualProspectiveReserve P K v n (t + 1) b π) := by
  let S := annualSurvivalMass P K t
  let T := annualSurvivalMass P K (t + 1)
  let D := annualDeathMass P K t
  let V := annualProspectiveReserve P K v n t b π
  let W := annualProspectiveReserve P K v n (t + 1) b π
  have hs : S ≠ 0 := ne_of_gt hS
  have hmass : S * V = ∫ ω, annualFutureLoss K v n t b π ω ∂P :=
    annualReserve_mass_identity P K hK v n t b π hS
  have hmassNext : T * W =
      ∫ ω, annualFutureLoss K v n (t + 1) b π ω ∂P :=
    annualReserve_mass_identity P K hK v n (t + 1) b π hNext
  have htotal : S * V + π * S = v * (b * D + T * W) := by
    rw [hmass, hmassNext]
    exact annualFutureLoss_integral_one_step P K hK v n t b π ht
  change V + π = v * (D / S * b + T / S * W)
  calc
    V + π = (S * V + π * S) / S := by
      field_simp [hs]
    _ = v * (b * D + T * W) / S := by rw [htotal]
    _ = v * (D / S * b + T / S * W) := by
      field_simp [hs]
