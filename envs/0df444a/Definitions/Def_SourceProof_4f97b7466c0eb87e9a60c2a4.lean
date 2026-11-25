-- Prove2me | Definitions.Def_SourceProof_4f97b7466c0eb87e9a60c2a4
-- name    : SourceProof_4f97b7466c0eb87e9a60c2a4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:22:47.289844+00:00
-- url     : https://prove2.me/theorems/71a3fdca-15d6-47e8-a73e-dd12752ee619
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.isSimplePredictable_leftSample_of_stoppingValues

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_SourceProof_c016c088ffde04a6620148ac

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left sampling and increment-only Riemann sums on random partitions

The sampled process reuses the deterministic left-step owner pathwise. Its
initial value is the original initial value. The Riemann sum, in contrast,
contains only increments, so its formula subtracts the source initial product.
Repeated endpoints and arbitrary finite stopping endpoints remain legal.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_4f97b7466c0eb87e9a60c2a4 (π : StoppingTimePartition F)
    {Y : ℝ≥0 → Ω → ℝ} (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω)) :
    IsSimplePredictable (π.leftSampleProcess Y) F :=
  ⟨π.leftSampleRep Y h0 hcoef, (_root_.Prove2MeSourceProof.h_c016c088ffde04a6620148ac π) Y h0 hcoef⟩
end ProbabilityTheory.StoppingTimePartition


