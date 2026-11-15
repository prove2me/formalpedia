-- Prove2me | Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
-- name    : Kyprianou_Ch02_LargeJumpProcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T10:24:47.290045+00:00
-- url     : https://prove2.me/theorems/b1ec2718-ae5f-4066-9af2-75b5af5a2a9a
-- title:
--   Large-jump Poisson integral at the strict unit cutoff
-- statement:
--   The process is the Poisson stochastic integral over 0<s<=t and |x|>=1, equal to zero at zero large-jump rate.
-- source:
--   Kyprianou (2006), Chapter 2, Eq. (2.3), pp. 34–35 and §2.2.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

/-- The uncompensated Lévy jumps of size at least one, including the
    zero-intensity case when this is the zero process. -/
noncomputable def largeJumpProcess
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P levyMeasure)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}),
    z.2 ∂(N.N ω)

end Kyprianou


