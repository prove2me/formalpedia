-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_VectorTaylorSums_F000
-- name    : StochLean_Probability_Process_Partition_VectorTaylorSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:32.923848+00:00
-- url     : https://prove2.me/theorems/eab85885-8a91-4296-9cbe-e79b4de9da36
-- title:
--   StochLean: Probability.Process.Partition.VectorTaylorSums F000

import Definitions.Def_StochLean_Analysis_PathVariation_VectorTaylorSums_F000
import Definitions.Def_StochLean_ForMathlib_Analysis_FiniteCoordinateDerivatives_F000
import Definitions.Def_StochLean_Probability_Process_Partition_WeightedCrossSums_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact coordinate Taylor sums on finite stopping-time partitions

Every derivative term is an existing scalar left-Riemann or weighted mixed
sum. The partial terminal cell and all ordered coordinate pairs are retained.
-/

@[expose] public section

open MeasureTheory Finset StochLean
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
  {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def frechetTaylorErrorProcess (π : StoppingTimePartition F)
    (f : (ι → ℝ) → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
  frechetTaylorErrorSum (π.path ω) f (fun u i ↦ X i u ω) t
end ProbabilityTheory.StoppingTimePartition


