-- Prove2me | Definitions.Def_Kyprianou_Ch02_SquareIntegrableMartingaleSpaceV4
-- name    : Kyprianou_Ch02_SquareIntegrableMartingaleSpaceV4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T12:33:13.466044+00:00
-- url     : https://prove2.me/theorems/8ff554fa-8c42-495a-8860-21cd980a7786
-- title:
--   Definition 2.11: genuinely finite-horizon square-integrable martingales
-- statement:
--   The source M^2_T predicate uses martingale behaviour only on [0,T]. The stopped process t ↦ M (min t T) is a martingale with respect to the supplied filtration, with zero mean and square integrability at times at most T and almost sure right-continuity on the finite horizon. Replaces an overrestrictive all-times martingale predicate.
-- source:
--   Kyprianou (2006) Definition 2.11, original PDF physical p.29, printed p.47, corrected 2026-11-17

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
noncomputable def IsSquareIntegrableMartingaleOnCh02V4
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (T : ℝ≥0) (M : ℝ≥0 → Ω → ℝ) : Prop :=
  MeasureTheory.Martingale (fun t ω => M (min t T) ω) ℱ P ∧
  (∀ t : ℝ≥0, t ≤ T →
    MemLp (M t) 2 P ∧ ∫ ω, M t ω ∂P = 0) ∧
  (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
    ContinuousWithinAt (fun s => M s ω) (Set.Icc t T) t)

end Ch02
end Kyprianou


