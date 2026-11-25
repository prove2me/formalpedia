-- Prove2me | Definitions.Def_SourceProof_7062939edfbaae600c8a129c
-- name    : SourceProof_7062939edfbaae600c8a129c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:10:11.565492+00:00
-- url     : https://prove2.me/theorems/a75329f7-49ee-5a30-97f9-ff962f1a67b1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.monotone_continuousQuadraticVariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000

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
theorem _root_.Prove2MeSourceProof.h_7062939edfbaae600c8a129c
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    Monotone (fun t ↦ hX.continuousQuadraticVariation hF t ω) :=
  (StochLean.stieltjesContinuousPart _).mono
end IsSemimartingale

end ProbabilityTheory


