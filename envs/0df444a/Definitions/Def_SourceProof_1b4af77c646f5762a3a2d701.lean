-- Prove2me | Definitions.Def_SourceProof_1b4af77c646f5762a3a2d701
-- name    : SourceProof_1b4af77c646f5762a3a2d701
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:04:15.296961+00:00
-- url     : https://prove2.me/theorems/36350f81-8ba9-48b5-bc08-37339cbb2ced
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.quadraticCovariationSumProcess_self

import Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
import Definitions.Def_SourceProof_3587e42ab751ce8dbe6b91ef

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

@[simp] theorem _root_.Prove2MeSourceProof.h_1b4af77c646f5762a3a2d701 (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess X X = π.quadraticVariationSumProcess X := by
  funext t ω
  simp only [ProbabilityTheory.StoppingTimePartition.quadraticCovariationSumProcess, ProbabilityTheory.StoppingTimePartition.quadraticVariationSumProcess,
    _root_.Prove2MeSourceProof.h_3587e42ab751ce8dbe6b91ef, pow_two]
end ProbabilityTheory.StoppingTimePartition


