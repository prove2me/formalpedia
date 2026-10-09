-- Prove2me | solution 2 for ActuarialValuation.annualReserve_mass_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:21:11.464711+00:00
-- url     : https://prove2.me/submissions/f1853277-87a9-4155-95cf-aaf082d14004

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
import Definitions.Def_actuarial_annualProspectiveReserve
import Definitions.Def_actuarial_annualSurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ)
  (hK : Measurable K) (v : ℝ) (n t : ℕ) (b π : ℝ)
  (hS : 0 < annualSurvivalMass P K t) :
  annualSurvivalMass P K t *
    annualProspectiveReserve P K v n t b π =
    ∫ ω, annualFutureLoss K v n t b π ω ∂P := by
  unfold annualProspectiveReserve
  exact mul_div_cancel₀ _ (ne_of_gt hS)
