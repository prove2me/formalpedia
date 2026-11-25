-- Prove2me | Definitions.Def_SourceProof_33b4740ce8fec4b85a3add51
-- name    : SourceProof_33b4740ce8fec4b85a3add51
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:53.318829+00:00
-- url     : https://prove2.me/theorems/b48142f3-2b00-4bf2-b60b-4a2ad5939dc5
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.leftRiemannSum_rightLimitProcess

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_SourceProof_6e177446f1dbadab2f5e1fc0
import Definitions.Def_SourceProof_ec912c886c06db43468f3a9e
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact random Riemann sums of a right-limit source step process

Every source endpoint is moved to its ceiling in the sampling partition.
The formula is pathwise for arbitrary integrators and includes no initial
product because the left Riemann sum is increment-only.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_33b4740ce8fec4b85a3add51 (H : SimplePredictableRep F)
    (π : StoppingTimePartition F) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.leftRiemannSumProcess (rightLimitProcess H.toProcess) X t ω =
      ∑ j : Fin H.partition.size, H.coefficient j ω *
        (X (min ((π.path ω).ceilingPoint (H.partition.point j.succ ω)) t) ω -
          X (min ((π.path ω).ceilingPoint (H.partition.point j.castSucc ω)) t) ω) := by
  unfold ProbabilityTheory.StoppingTimePartition.leftRiemannSumProcess
  simp_rw [(_root_.Prove2MeSourceProof.h_ec912c886c06db43468f3a9e H), Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (_root_.Prove2MeSourceProof.h_6e177446f1dbadab2f5e1fc0 (π.path ω)) ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (H.partition.path ω)) j)
    (H.coefficient j ω) (fun u ↦ X (min u t) ω)
end ProbabilityTheory.SimplePredictableRep


