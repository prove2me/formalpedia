-- Prove2me | Definitions.Def_SourceProof_2b513c204954b4445bde4e1f
-- name    : SourceProof_2b513c204954b4445bde4e1f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:11:48.371042+00:00
-- url     : https://prove2.me/theorems/07d75d3c-75f4-43f5-8745-6a8817b39648
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.leftSampleProcess_zero_process

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_31ff967a98c1d14a8d4b3841

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left sampling is a compact-deviation contraction

The bound is uniform over arbitrary random partitions and requires no path
regularity or measurability. It does not assert that sampling a discontinuous
path on finer partitions converges uniformly to its left-limit process.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {l : Filter ι} {X Y : ℝ≥0 → Ω → ℝ}

namespace StoppingTimePartition
@[simp] theorem _root_.Prove2MeSourceProof.h_2b513c204954b4445bde4e1f
    (π : StoppingTimePartition F) : π.leftSampleProcess (0 : ℝ≥0 → Ω → ℝ) = 0 := by
  funext t ω
  exact congrFun (_root_.Prove2MeSourceProof.h_31ff967a98c1d14a8d4b3841 (π.path ω)) t
end StoppingTimePartition

end ProbabilityTheory


