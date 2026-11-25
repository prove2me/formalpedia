-- Prove2me | Definitions.Def_SourceProof_6ba263283c3260d9aff2f33e
-- name    : SourceProof_6ba263283c3260d9aff2f33e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:47:09.026149+00:00
-- url     : https://prove2.me/theorems/06725a46-612e-4d8f-a820-0fc9f6347865
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_indicator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_InitialMask_F000
import Definitions.Def_SourceProof_44275880bd3026f520cb5dfd
import Definitions.Def_SourceProof_ba15608e2ab7164b205d1611
import Definitions.Def_SourceProof_d9146a341c2877565a0adcfb
import Definitions.Def_SourceProof_ec04cdbdbe92b05b4697a078

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial-event masks of source simple predictable processes

An initial measurable event is measurable at every source left stopping endpoint.
Masking retains the same partition, including repeated endpoints, and commutes
pathwise with both the terminal elementary integral and its process version.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ} {s : Set Ω}

theorem _root_.Prove2MeSourceProof.h_6ba263283c3260d9aff2f33e (hH : IsSimplePredictable H F)
    (hs : MeasurableSet[F 0] s) (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_ba15608e2ab7164b205d1611 hH) hs).elementaryIntegral X = s.indicator (hH.elementaryIntegral X) := by
  have heq : (hH.choose.initialMask s hs).toProcess = fun t ↦ s.indicator (H t) := by
    rw [_root_.Prove2MeSourceProof.h_44275880bd3026f520cb5dfd, hH.choose_spec]
  rw [(_root_.Prove2MeSourceProof.h_ec04cdbdbe92b05b4697a078 ((_root_.Prove2MeSourceProof.h_ba15608e2ab7164b205d1611 hH) hs)) _ heq,
    _root_.Prove2MeSourceProof.h_d9146a341c2877565a0adcfb]
  rfl
end IsSimplePredictable
end ProbabilityTheory


