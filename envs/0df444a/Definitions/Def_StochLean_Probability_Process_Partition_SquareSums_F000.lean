-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_SquareSums_F000
-- name    : StochLean_Probability_Process_Partition_SquareSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:40:59.693484+00:00
-- url     : https://prove2.me/theorems/7a065751-fe71-5ef2-aa57-a9c212f1de9a
-- title:
--   StochLean: Probability.Process.Partition.SquareSums F000

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Raw square-increment sums on stopping-time partitions

The pure deterministic square-sum owner is reused pathwise. The source initial
square is added exactly once. The telescoping identity is valid for arbitrary
real paths and repeated endpoints; no regularity hypothesis is required.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def quadraticVariationSumProcess (π : StoppingTimePartition F) (X : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ (X 0 ω) ^ 2 +
      StochLean.quadraticVariationSum (π.path ω) (fun u ↦ X (min u t) ω)
end ProbabilityTheory.StoppingTimePartition


