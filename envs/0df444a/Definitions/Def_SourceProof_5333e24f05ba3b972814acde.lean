-- Prove2me | Definitions.Def_SourceProof_5333e24f05ba3b972814acde
-- name    : SourceProof_5333e24f05ba3b972814acde
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:42:09.553047+00:00
-- url     : https://prove2.me/theorems/f1d4e243-98bb-5c47-b21c-1c46af2af9e1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.isSquareIntegrableMartingale_elementaryIntegralProcess

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_a53e1079902a6b3cf35932b1
import Definitions.Def_SourceProof_da50a9b4aa24d95cd193edfb
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Adapted
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
theorem _root_.Prove2MeSourceProof.h_5333e24f05ba3b972814acde
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (hX : IsSquareIntegrableMartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    IsSquareIntegrableMartingale (hH.elementaryIntegralProcess X) F P :=
  ⟨(_root_.Prove2MeSourceProof.h_a53e1079902a6b3cf35932b1 hH) hX.1 hF hr C hb,
    fun t ↦ (_root_.Prove2MeSourceProof.h_da50a9b4aa24d95cd193edfb hH) hX.1 hF hr t (hX.2 t) C hb⟩
end IsSimplePredictable

end ProbabilityTheory


