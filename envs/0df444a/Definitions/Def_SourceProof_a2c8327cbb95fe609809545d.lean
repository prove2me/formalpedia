-- Prove2me | Definitions.Def_SourceProof_a2c8327cbb95fe609809545d
-- name    : SourceProof_a2c8327cbb95fe609809545d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:10:20.406578+00:00
-- url     : https://prove2.me/theorems/591a4394-351e-5f35-8e8f-abdb86d195af
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.adapted_continuousQuadraticVariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_4c53178c24a5f39c8484090d
import Definitions.Def_SourceProof_b39c46ea153c4c96354bca13

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
theorem _root_.Prove2MeSourceProof.h_a2c8327cbb95fe609809545d
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Adapted F (hX.continuousQuadraticVariation hF) :=
  _root_.Prove2MeSourceProof.h_b39c46ea153c4c96354bca13
    (Classical.choice ((_root_.Prove2MeSourceProof.h_4c53178c24a5f39c8484090d hX) hX hF)).left_adapted
end IsSemimartingale

end ProbabilityTheory


