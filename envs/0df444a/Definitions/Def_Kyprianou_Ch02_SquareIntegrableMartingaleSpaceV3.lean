-- Prove2me | Definitions.Def_Kyprianou_Ch02_SquareIntegrableMartingaleSpaceV3
-- name    : Kyprianou_Ch02_SquareIntegrableMartingaleSpaceV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T19:22:21.82665+00:00
-- url     : https://prove2.me/theorems/7fb94082-6949-45b3-83ab-4804a0cc4f31
-- title:
--   Definition 2.11: centred right-continuous L2 martingale space on a finite horizon
-- statement:
--   The space of zero-mean square-integrable martingales on a finite time horizon, whose paths are right-continuous relative to the completed right-continuous filtration.
-- source:
--   Kyprianou (2006), Definition 2.11, p. 47

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

namespace Ch02

/-- The space M^2_T of centred square-integrable martingales with
    almost surely right-continuous sample paths on [0,T]. -/
noncomputable def IsSquareIntegrableMartingaleOnCh02
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (T : ℝ≥0) (M : ℝ≥0 → Ω → ℝ) : Prop :=
  MeasureTheory.Martingale M ℱ P ∧
  (∀ t : ℝ≥0, t ≤ T →
    MemLp (M t) 2 P ∧ ∫ ω, M t ω ∂P = 0) ∧
  (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
    ContinuousWithinAt (fun s => M s ω) (Set.Icc t T) t)

end Ch02
end Kyprianou


