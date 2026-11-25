-- Prove2me | Definitions.Def_SourceProof_8a4a12d702db4efcb2478f93
-- name    : SourceProof_8a4a12d702db4efcb2478f93
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:19:28.678952+00:00
-- url     : https://prove2.me/theorems/8280973a-9fc8-5fbb-96a0-1a49fda85013
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasFiniteVariationPaths_continuousQuadraticVariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_6ed3c177b9234dc2ab8ed747
import Definitions.Def_SourceProof_7062939edfbaae600c8a129c

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous component of the unique raw quadratic variation

The definition removes the point atoms of a genuine Stieltjes version of the
already constructed raw bracket. It is not a second quadratic-variation
construction. Its exact decomposition uses the squared jumps of the original
semimartingale, with the initial square separate and summability proved.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_8a4a12d702db4efcb2478f93
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (hX.continuousQuadraticVariation hF) P :=
  (_root_.Prove2MeSourceProof.h_6ed3c177b9234dc2ab8ed747 (show ProbabilityTheory.HasMonotonePaths (hX.continuousQuadraticVariation hF) P from
    Eventually.of_forall ((_root_.Prove2MeSourceProof.h_7062939edfbaae600c8a129c hX) hF)))
end IsSemimartingale

end ProbabilityTheory


