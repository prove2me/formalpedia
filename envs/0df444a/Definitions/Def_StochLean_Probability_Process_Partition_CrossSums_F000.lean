-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
-- name    : StochLean_Probability_Process_Partition_CrossSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:51:10.177928+00:00
-- url     : https://prove2.me/theorems/b87a0af0-9548-5925-a2c3-f4dcae070bdb
-- title:
--   StochLean: Probability.Process.Partition.CrossSums F000

import Definitions.Def_StochLean_Probability_Process_Partition_SquareSums_F000

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

def quadraticCovariationSumProcess (π : StoppingTimePartition F) (X Y : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ X 0 ω * Y 0 ω +
      StochLean.covariationSum (π.path ω) (fun u ↦ X (min u t) ω) (fun u ↦ Y (min u t) ω)
end ProbabilityTheory.StoppingTimePartition


