-- Prove2me | Definitions.Def_SourceProof_44275880bd3026f520cb5dfd
-- name    : SourceProof_44275880bd3026f520cb5dfd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:46:06.676605+00:00
-- url     : https://prove2.me/theorems/6431e5b2-c2ae-5928-8282-bb135e613d3d
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_initialMask

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_InitialMask_F000

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

theorem _root_.Prove2MeSourceProof.h_44275880bd3026f520cb5dfd (H : SimplePredictableRep F) {s : Set Ω}
    (hs : MeasurableSet[F 0] s) :
    (H.initialMask s hs).toProcess = fun t ↦ s.indicator (H.toProcess t) := by
  classical
  funext t ω
  change (if t = 0 then s.indicator H.initial ω else
    ∑ i : Fin H.partition.size,
      if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
      then s.indicator (H.coefficient i) ω else 0) = s.indicator ((ProbabilityTheory.SimplePredictableRep.toProcess H) t) ω
  by_cases hω : ω ∈ s <;> simp [ProbabilityTheory.SimplePredictableRep.toProcess, hω]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ} {s : Set Ω}

end IsSimplePredictable
end ProbabilityTheory


