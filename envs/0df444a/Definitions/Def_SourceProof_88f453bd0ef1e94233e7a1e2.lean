-- Prove2me | Definitions.Def_SourceProof_88f453bd0ef1e94233e7a1e2
-- name    : SourceProof_88f453bd0ef1e94233e7a1e2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:28:07.609496+00:00
-- url     : https://prove2.me/theorems/54194039-7807-4182-bd3b-8a6a75df1121
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.leftSampleProcess_zero

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_SourceProof_4ffa320b02b60d0dbe7bd7da

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

@[simp] theorem _root_.Prove2MeSourceProof.h_88f453bd0ef1e94233e7a1e2 (π : StoppingTimePartition F)
    (Y : ℝ≥0 → Ω → ℝ) : π.leftSampleProcess Y 0 = Y 0 := by
  funext ω
  exact (_root_.Prove2MeSourceProof.h_4ffa320b02b60d0dbe7bd7da (π.path ω)) _
end ProbabilityTheory.StoppingTimePartition


