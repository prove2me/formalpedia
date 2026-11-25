-- Prove2me | Definitions.Def_SourceProof_18476b90b4b71a8ada4a076c
-- name    : SourceProof_18476b90b4b71a8ada4a076c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:55:54.826257+00:00
-- url     : https://prove2.me/theorems/05c2cb56-ca2f-5e4b-9bb4-483a8918d9a4
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_indicator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_6ba263283c3260d9aff2f33e
import Definitions.Def_SourceProof_ba15608e2ab7164b205d1611

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

theorem _root_.Prove2MeSourceProof.h_18476b90b4b71a8ada4a076c (hH : IsSimplePredictable H F)
    (hs : MeasurableSet[F 0] s) (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_ba15608e2ab7164b205d1611 hH) hs).elementaryIntegralProcess X =
      fun t ↦ s.indicator (hH.elementaryIntegralProcess X t) := by
  funext t
  exact (_root_.Prove2MeSourceProof.h_6ba263283c3260d9aff2f33e hH) hs _
end IsSimplePredictable
end ProbabilityTheory


