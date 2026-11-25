-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_InitialMask_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_InitialMask_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:31.251897+00:00
-- url     : https://prove2.me/theorems/ae72bf6a-08b1-471f-b3bf-b24d329a0c99
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.InitialMask F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001

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

noncomputable def initialMask (H : SimplePredictableRep F) (s : Set Ω)
    (hs : MeasurableSet[F 0] s) : SimplePredictableRep F where
  partition := H.partition
  initial := s.indicator H.initial
  measurable_initial := H.measurable_initial.indicator hs
  coefficient := fun i ↦ s.indicator (H.coefficient i)
  measurable_coefficient := fun i ↦ (H.measurable_coefficient i).indicator
    ((H.partition.point i.castSucc).isStoppingTime.le_measurableSpace_of_const_le
      (fun _ ↦ bot_le) s hs)
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ} {s : Set Ω}

end IsSimplePredictable
end ProbabilityTheory


