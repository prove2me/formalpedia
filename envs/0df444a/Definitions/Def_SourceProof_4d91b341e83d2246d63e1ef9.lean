-- Prove2me | Definitions.Def_SourceProof_4d91b341e83d2246d63e1ef9
-- name    : SourceProof_4d91b341e83d2246d63e1ef9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:21:54.867142+00:00
-- url     : https://prove2.me/theorems/a0815c2a-3145-419e-a4f0-948e8ef31ff7
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.quadraticCovariationSumProcess_const_mul_left

import Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
import Definitions.Def_SourceProof_312e6109268d36a0082cb298

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Raw mixed increment sums and their pointwise algebra

The original pure deterministic covariation sum is used, with the separate
initial product. No adaptedness, regularity or integrability is needed here.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_4d91b341e83d2246d63e1ef9 (π : StoppingTimePartition F)
    (X Y : ℝ≥0 → Ω → ℝ) (c : ℝ) :
    π.quadraticCovariationSumProcess (fun t ω ↦ c * X t ω) Y =
      c • π.quadraticCovariationSumProcess X Y := by
  funext t ω
  simp only [ProbabilityTheory.StoppingTimePartition.quadraticCovariationSumProcess, _root_.Prove2MeSourceProof.h_312e6109268d36a0082cb298,
    Pi.smul_apply, smul_eq_mul]
  ring
end ProbabilityTheory.StoppingTimePartition


