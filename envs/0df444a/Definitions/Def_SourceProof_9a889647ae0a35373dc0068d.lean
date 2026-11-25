-- Prove2me | Definitions.Def_SourceProof_9a889647ae0a35373dc0068d
-- name    : SourceProof_9a889647ae0a35373dc0068d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:19:38.017405+00:00
-- url     : https://prove2.me/theorems/4dc41f28-d9fb-527a-ae4c-78acb9bd6ce6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasContinuousPaths_continuousQuadraticVariation

import Definitions.Def_SourceProof_ac2ebac4addb5d2fcfe359a6

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
theorem _root_.Prove2MeSourceProof.h_9a889647ae0a35373dc0068d
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasContinuousPaths (hX.continuousQuadraticVariation hF) P :=
  Eventually.of_forall ((_root_.Prove2MeSourceProof.h_ac2ebac4addb5d2fcfe359a6 hX) hF)
end IsSemimartingale

end ProbabilityTheory


