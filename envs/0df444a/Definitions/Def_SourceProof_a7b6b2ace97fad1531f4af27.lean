-- Prove2me | Definitions.Def_SourceProof_a7b6b2ace97fad1531f4af27
-- name    : SourceProof_a7b6b2ace97fad1531f4af27
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:44:34.675052+00:00
-- url     : https://prove2.me/theorems/1da16f39-f761-50a8-9d79-ac11e8298b6e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation_nonneg

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_7062939edfbaae600c8a129c
import Definitions.Def_SourceProof_b2af300e8e7381ed92a14088

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Version invariance and continuous-path specialization of the continuous bracket -/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_a7b6b2ace97fad1531f4af27
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (t : ℝ≥0) (ω : Ω) :
    0 ≤ hX.continuousQuadraticVariation hF t ω := by
  rw [← (_root_.Prove2MeSourceProof.h_b2af300e8e7381ed92a14088 hX) hF ω]
  exact (_root_.Prove2MeSourceProof.h_7062939edfbaae600c8a129c hX) hF ω (show (0 : ℝ≥0) ≤ t from bot_le)
end IsSemimartingale

end ProbabilityTheory


