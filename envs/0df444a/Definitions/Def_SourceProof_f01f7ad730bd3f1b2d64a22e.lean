-- Prove2me | Definitions.Def_SourceProof_f01f7ad730bd3f1b2d64a22e
-- name    : SourceProof_f01f7ad730bd3f1b2d64a22e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:28.859284+00:00
-- url     : https://prove2.me/theorems/c104a0fe-aafa-41a0-baba-61596ad8da90
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.isStoppingTime_firstExit

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_InitialMask_F000
import Definitions.Def_SourceProof_08f35e40de15386d6fd32725
import Definitions.Def_SourceProof_877ba5ad1fd0d646fb6c666f
import Definitions.Def_SourceProof_d0ba14a65d084d5914c41424

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded source truncation at a left-continuous first exit

The initial event `{τ > 0}` is indispensable: the source class allows an arbitrary
initial value and a distinct right limit at zero. The closed cutoff is bounded by
the threshold on this event and its elementary integral agrees strictly before `τ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

variable [F.IsRightContinuous]

theorem _root_.Prove2MeSourceProof.h_f01f7ad730bd3f1b2d64a22e (hH : IsSimplePredictable H F) (a : ℝ) :
    IsStoppingTime F (hittingAfter H {x | a < ‖x‖} 0) :=
  (_root_.Prove2MeSourceProof.h_877ba5ad1fd0d646fb6c666f (_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 hH))
    (fun ω ↦ ((_root_.Prove2MeSourceProof.h_08f35e40de15386d6fd32725 hH) ω).1) (isOpen_lt continuous_const continuous_norm) 0
end IsSimplePredictable
end ProbabilityTheory


