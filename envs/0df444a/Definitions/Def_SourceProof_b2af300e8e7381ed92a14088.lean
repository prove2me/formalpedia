-- Prove2me | Definitions.Def_SourceProof_b2af300e8e7381ed92a14088
-- name    : SourceProof_b2af300e8e7381ed92a14088
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:25:56.207392+00:00
-- url     : https://prove2.me/theorems/aa81cb58-a8b2-4ce9-a3ec-380ecc5c02e2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation_zero

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_6dedeeef2014456de8ce028c

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
theorem _root_.Prove2MeSourceProof.h_b2af300e8e7381ed92a14088
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    hX.continuousQuadraticVariation hF 0 ω = 0 := _root_.Prove2MeSourceProof.h_6dedeeef2014456de8ce028c _
end IsSemimartingale

end ProbabilityTheory


