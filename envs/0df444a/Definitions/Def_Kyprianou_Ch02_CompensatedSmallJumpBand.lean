-- Prove2me | Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
-- name    : Kyprianou_Ch02_CompensatedSmallJumpBand
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T10:25:19.758502+00:00
-- url     : https://prove2.me/theorems/fe7bdae5-6339-45d3-9d80-f7d1ec989c28
-- title:
--   Compensated Poisson integral on finite small-jump bands
-- statement:
--   The compensated integral over epsilon<=|x|<1, retaining the deterministic compensator and all finite-band jumps.
-- source:
--   Kyprianou (2006), Chapter 2, Eq. (2.18), p. 52.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

/-- Finite-band compensated Poisson sum for epsilon <= |x| < 1.
    The full small-jump martingale is obtained by removing epsilon. -/
noncomputable def compensatedSmallJumpBand
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P levyMeasure)
    (ε : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
      {x : ℝ | ε ≤ |x| ∧ |x| < 1}), z.2 ∂(N.N ω)) -
    (t : ℝ) * (∫ x in {x : ℝ | ε ≤ |x| ∧ |x| < 1}, x ∂levyMeasure)

end Kyprianou


