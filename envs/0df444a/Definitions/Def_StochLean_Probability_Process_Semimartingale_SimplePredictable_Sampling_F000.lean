-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Sampling_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_Sampling_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:14.23321+00:00
-- url     : https://prove2.me/theorems/63d3e75b-fe01-42c9-b1b5-98dab356136a
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.Sampling F000

import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Normalization_F000
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Moments.Variance

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The elementary integral as an existing discrete predictable integral

The coefficient at index `n + 1` is measurable at the original left stopping endpoint, even
when the integrator is stopped at a deterministic horizon. No deterministic bound on the
partition endpoints, or change to their sigma-fields, is imposed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def discreteCoefficient (H : SimplePredictableRep F) : ℕ → Ω → ℝ
  | 0 => 0
  | n + 1 => if hn : n < H.partition.size then H.coefficient ⟨n, hn⟩ else 0
end ProbabilityTheory.SimplePredictableRep


