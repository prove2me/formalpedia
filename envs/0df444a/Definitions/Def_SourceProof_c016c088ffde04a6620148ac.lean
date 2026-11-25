-- Prove2me | Definitions.Def_SourceProof_c016c088ffde04a6620148ac
-- name    : SourceProof_c016c088ffde04a6620148ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:53:46.988955+00:00
-- url     : https://prove2.me/theorems/bbdabc0f-1566-4b5f-9fd8-d6e2a36c2be7
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.toProcess_leftSampleRep

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001

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

theorem _root_.Prove2MeSourceProof.h_c016c088ffde04a6620148ac (π : StoppingTimePartition F) (Y : ℝ≥0 → Ω → ℝ)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω)) :
    (π.leftSampleRep Y h0 hcoef).toProcess = π.leftSampleProcess Y := by
  classical
  funext t ω
  simp only [ProbabilityTheory.SimplePredictableRep.toProcess, ProbabilityTheory.StoppingTimePartition.leftSampleRep, ProbabilityTheory.StoppingTimePartition.leftSampleProcess,
    StochLean.TimePartition.leftStep, Set.indicator_apply, mem_Ioc]
  rfl
end ProbabilityTheory.StoppingTimePartition


