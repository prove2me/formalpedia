-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_TaylorSums_F000
-- name    : StochLean_Probability_Process_Partition_TaylorSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:08.201006+00:00
-- url     : https://prove2.me/theorems/dd03c5a8-fec5-4772-a249-e75bdd3e155b
-- title:
--   StochLean: Probability.Process.Partition.TaylorSums F000

import Definitions.Def_StochLean_Analysis_PathVariation_TaylorSums_F000
import Definitions.Def_StochLean_Probability_Process_Partition_WeightedCrossSums_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact Taylor error process on finite stopping-time partitions -/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def quadraticTaylorErrorProcess (π : StoppingTimePartition F)
    (f : ℝ → ℝ) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
  StochLean.quadraticTaylorErrorSum (π.path ω) f (X · ω) t
end ProbabilityTheory.StoppingTimePartition


