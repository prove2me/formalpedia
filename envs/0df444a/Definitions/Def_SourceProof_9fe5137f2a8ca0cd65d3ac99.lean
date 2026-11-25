-- Prove2me | Definitions.Def_SourceProof_9fe5137f2a8ca0cd65d3ac99
-- name    : SourceProof_9fe5137f2a8ca0cd65d3ac99
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:33:15.101971+00:00
-- url     : https://prove2.me/theorems/bde1267e-1035-4c73-a1fe-6c91aed8d064
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.martingale_integralProcess

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Normalization_F000
import Definitions.Def_SourceProof_3c6f939081c92d53dd602282
import Definitions.Def_SourceProof_7d58eb4e8ca0b9afe6bb32b4
import Definitions.Def_SourceProof_992fdf07bd2378bc3aafe3c8
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_b1eb338f14932f1513d6a139
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

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_9fe5137f2a8ca0cd65d3ac99
    (H : SimplePredictableRep F) (hX : Martingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (C : ℝ≥0)
    (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) : Martingale (H.integralProcess X) F P := by
  have heq := (_root_.Prove2MeSourceProof.h_b1eb338f14932f1513d6a139 H.removeEmptyIntervals) H (_root_.Prove2MeSourceProof.h_992fdf07bd2378bc3aafe3c8 H) X
  rw [← heq]
  apply (_root_.Prove2MeSourceProof.h_3c6f939081c92d53dd602282 H.removeEmptyIntervals) hX hF hr C
  · apply ae_of_all
    intro ω
    change ‖H.initial ω‖ ≤ (C : ℝ)
    simpa only [(_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417 H)] using hb 0 ω
  · intro i
    exact ae_of_all P ((_root_.Prove2MeSourceProof.h_7d58eb4e8ca0b9afe6bb32b4 H) C.coe_nonneg hb i)
end SimplePredictableRep

end ProbabilityTheory


