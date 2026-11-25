-- Prove2me | Definitions.Def_SourceProof_efe23ccbf6a82dd59df5d03e
-- name    : SourceProof_efe23ccbf6a82dd59df5d03e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:47:14.945955+00:00
-- url     : https://prove2.me/theorems/936ab55b-8d43-4eca-8b39-e16824ceb4ee
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.leftRiemannSumProcess_sub_integrand

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of increment-only left Riemann sums

These pointwise identities impose no regularity or measurability assumptions.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_efe23ccbf6a82dd59df5d03e (π : StoppingTimePartition F)
    (Y Z X : ℝ≥0 → Ω → ℝ) :
    π.leftRiemannSumProcess (Y - Z) X =
      π.leftRiemannSumProcess Y X - π.leftRiemannSumProcess Z X := by
  funext t ω
  simp only [ProbabilityTheory.StoppingTimePartition.leftRiemannSumProcess, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end ProbabilityTheory.StoppingTimePartition


