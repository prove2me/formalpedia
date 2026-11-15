-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.girsanov_density_preserves_brownian_continuous_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:15:09.658708+00:00
-- url     : https://prove2.me/submissions/bb923212-f5ed-4301-bcf8-52b3c99280cd

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (Z : Ω -> ℝ) :
    ∀ᵐ omega ∂(P.withDensity (fun omega => ENNReal.ofReal (Z omega))),
      Continuous (fun t : ℝ => W.W t omega) := by
  exact (withDensity_absolutelyContinuous P
    (fun omega => ENNReal.ofReal (Z omega))).ae_le W.continuous_paths
