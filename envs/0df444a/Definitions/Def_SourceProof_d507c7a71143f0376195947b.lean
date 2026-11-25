-- Prove2me | Definitions.Def_SourceProof_d507c7a71143f0376195947b
-- name    : SourceProof_d507c7a71143f0376195947b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:17.767589+00:00
-- url     : https://prove2.me/theorems/d943da71-9305-5df3-bc5c-fdde1f874f1d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_firstExitTruncation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
import Definitions.Def_SourceProof_18476b90b4b71a8ada4a076c
import Definitions.Def_SourceProof_ba15608e2ab7164b205d1611
import Definitions.Def_SourceProof_c9eacbbef1c8e0923f7b8eda
import Definitions.Def_SourceProof_ebaf9e73dbb24b573c624591
import Definitions.Def_SourceProof_f01f7ad730bd3f1b2d64a22e
import Definitions.Def_SourceProof_f2daf40b88ac8840065b16fc

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

theorem _root_.Prove2MeSourceProof.h_d507c7a71143f0376195947b (hH : IsSimplePredictable H F)
    (a : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_c9eacbbef1c8e0923f7b8eda hH) a).elementaryIntegralProcess X =
      fun t ↦ {ω | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω}.indicator
        (stoppedProcess (hH.elementaryIntegralProcess X) (hittingAfter H {x | a < ‖x‖} 0) t) := by
  change ((_root_.Prove2MeSourceProof.h_ba15608e2ab7164b205d1611 ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) ((_root_.Prove2MeSourceProof.h_f01f7ad730bd3f1b2d64a22e hH) a)))
    (((_root_.Prove2MeSourceProof.h_f01f7ad730bd3f1b2d64a22e hH) a).measurableSet_gt 0)).elementaryIntegralProcess X = _
  rw [(_root_.Prove2MeSourceProof.h_18476b90b4b71a8ada4a076c ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) ((_root_.Prove2MeSourceProof.h_f01f7ad730bd3f1b2d64a22e hH) a)))
      (((_root_.Prove2MeSourceProof.h_f01f7ad730bd3f1b2d64a22e hH) a).measurableSet_gt 0) X,
    (_root_.Prove2MeSourceProof.h_f2daf40b88ac8840065b16fc hH) ((_root_.Prove2MeSourceProof.h_f01f7ad730bd3f1b2d64a22e hH) a) X]
  rfl
end IsSimplePredictable
end ProbabilityTheory


