-- Prove2me | Definitions.Def_SourceProof_a53e1079902a6b3cf35932b1
-- name    : SourceProof_a53e1079902a6b3cf35932b1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:36:28.483187+00:00
-- url     : https://prove2.me/theorems/412b4860-b91a-5a0b-80b4-1e35f8c0d3ec
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.martingale_elementaryIntegralProcess

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_9fe5137f2a8ca0cd65d3ac99
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded elementary integrands preserve martingales

Random endpoints need not be deterministically bounded. Conditional increments
are computed after raising each endpoint to the conditioning time. Coefficients
on empty cells are normalized only when deducing a coefficient bound from a
process bound. The initial coefficient and initial martingale value are retained.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_a53e1079902a6b3cf35932b1 {H : ℝ≥0 → Ω → ℝ}
    (hH : IsSimplePredictable H F) (hX : Martingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    Martingale (hH.elementaryIntegralProcess X) F P :=
  (_root_.Prove2MeSourceProof.h_9fe5137f2a8ca0cd65d3ac99 hH.choose) hX hF hr C (by simpa only [hH.choose_spec] using hb)
end IsSimplePredictable

end ProbabilityTheory


