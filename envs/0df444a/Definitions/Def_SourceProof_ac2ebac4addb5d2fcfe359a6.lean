-- Prove2me | Definitions.Def_SourceProof_ac2ebac4addb5d2fcfe359a6
-- name    : SourceProof_ac2ebac4addb5d2fcfe359a6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:10:27.822365+00:00
-- url     : https://prove2.me/theorems/3dc23976-e91f-5b19-b1af-ae14c174ddb6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuous_continuousQuadraticVariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_6d3db110f0519c19963e703d

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
theorem _root_.Prove2MeSourceProof.h_ac2ebac4addb5d2fcfe359a6
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    Continuous (fun t ↦ hX.continuousQuadraticVariation hF t ω) :=
  _root_.Prove2MeSourceProof.h_6d3db110f0519c19963e703d _
end IsSemimartingale

end ProbabilityTheory


