-- Prove2me | Definitions.Def_SourceProof_d9146a341c2877565a0adcfb
-- name    : SourceProof_d9146a341c2877565a0adcfb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:36:46.666005+00:00
-- url     : https://prove2.me/theorems/f85e2ed8-7645-5779-bfea-e6afe96e17ef
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_initialMask

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

theorem _root_.Prove2MeSourceProof.h_d9146a341c2877565a0adcfb (H : SimplePredictableRep F) {s : Set Ω}
    (hs : MeasurableSet[F 0] s) (X : ℝ≥0 → Ω → ℝ) :
    (H.initialMask s hs).integral X = s.indicator (H.integral X) := by
  classical
  funext ω
  change s.indicator H.initial ω * X 0 ω + ∑ i : Fin H.partition.size,
    s.indicator (H.coefficient i) ω *
      (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω) =
        s.indicator ((ProbabilityTheory.SimplePredictableRep.integral H) X) ω
  by_cases hω : ω ∈ s <;> simp [ProbabilityTheory.SimplePredictableRep.integral, hω]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ} {s : Set Ω}

end IsSimplePredictable
end ProbabilityTheory


