-- Prove2me | Definitions.Def_SourceProof_824b0e2c6cd9530a7cfac3d4
-- name    : SourceProof_824b0e2c6cd9530a7cfac3d4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:56:40.759054+00:00
-- url     : https://prove2.me/theorems/5526e35b-e2ff-40a5-866e-3fe3b4690a8f
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.leftRiemannSumProcess_eq_integralProcess_sub_initial

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105

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

theorem _root_.Prove2MeSourceProof.h_824b0e2c6cd9530a7cfac3d4
    (π : StoppingTimePartition F) (Y X : ℝ≥0 → Ω → ℝ)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω)) :
    π.leftRiemannSumProcess Y X = fun t ω ↦
      (π.leftSampleRep Y h0 hcoef).integralProcess X t ω - Y 0 ω * X 0 ω := by
  funext t ω
  rw [_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105]
  change _ = Y 0 ω * X 0 ω + π.leftRiemannSumProcess Y X t ω - Y 0 ω * X 0 ω
  ring
end ProbabilityTheory.StoppingTimePartition


