-- Prove2me | Definitions.Def_SourceProof_ba15608e2ab7164b205d1611
-- name    : SourceProof_ba15608e2ab7164b205d1611
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:57:11.616332+00:00
-- url     : https://prove2.me/theorems/ba3edc84-7bc2-4871-b817-3b0f4f43e599
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.indicator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_InitialMask_F000
import Definitions.Def_SourceProof_44275880bd3026f520cb5dfd

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

theorem _root_.Prove2MeSourceProof.h_ba15608e2ab7164b205d1611 (hH : IsSimplePredictable H F) (hs : MeasurableSet[F 0] s) :
    IsSimplePredictable (fun t ↦ s.indicator (H t)) F := by
  refine ⟨hH.choose.initialMask s hs, ?_⟩
  rw [_root_.Prove2MeSourceProof.h_44275880bd3026f520cb5dfd, hH.choose_spec]
end IsSimplePredictable
end ProbabilityTheory


