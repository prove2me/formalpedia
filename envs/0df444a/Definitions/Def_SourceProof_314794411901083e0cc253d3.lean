-- Prove2me | Definitions.Def_SourceProof_314794411901083e0cc253d3
-- name    : SourceProof_314794411901083e0cc253d3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:24:44.215377+00:00
-- url     : https://prove2.me/theorems/0448e09d-0321-558f-9ef6-a99a6319da3e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSemimartingale_continuousQuadraticVariation

import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_2c0d4ca99a3f51a9d8eb6cb0
import Definitions.Def_SourceProof_8a4a12d702db4efcb2478f93
import Definitions.Def_SourceProof_9a889647ae0a35373dc0068d
import Definitions.Def_SourceProof_a2c8327cbb95fe609809545d

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
theorem _root_.Prove2MeSourceProof.h_314794411901083e0cc253d3
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.continuousQuadraticVariation hF) F P :=
  (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f ((_root_.Prove2MeSourceProof.h_8a4a12d702db4efcb2478f93 hX) hF))
    ((_root_.Prove2MeSourceProof.h_a2c8327cbb95fe609809545d hX) hF) hF
    (_root_.Prove2MeSourceProof.h_2c0d4ca99a3f51a9d8eb6cb0 ((_root_.Prove2MeSourceProof.h_9a889647ae0a35373dc0068d hX) hF))
end IsSemimartingale

end ProbabilityTheory


