-- Prove2me | Definitions.Def_SourceProof_c9eacbbef1c8e0923f7b8eda
-- name    : SourceProof_c9eacbbef1c8e0923f7b8eda
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:33.196282+00:00
-- url     : https://prove2.me/theorems/96f17325-ad78-56f0-a37f-9c81b46c21a9
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.firstExitTruncation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
import Definitions.Def_SourceProof_ba15608e2ab7164b205d1611
import Definitions.Def_SourceProof_ebaf9e73dbb24b573c624591
import Definitions.Def_SourceProof_f01f7ad730bd3f1b2d64a22e

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

theorem _root_.Prove2MeSourceProof.h_c9eacbbef1c8e0923f7b8eda (hH : IsSimplePredictable H F) (a : ℝ) :
    IsSimplePredictable (ProbabilityTheory.firstExitTruncation H a) F :=
  (_root_.Prove2MeSourceProof.h_ba15608e2ab7164b205d1611 ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) ((_root_.Prove2MeSourceProof.h_f01f7ad730bd3f1b2d64a22e hH) a)))
    (((_root_.Prove2MeSourceProof.h_f01f7ad730bd3f1b2d64a22e hH) a).measurableSet_gt 0)
end IsSimplePredictable
end ProbabilityTheory


