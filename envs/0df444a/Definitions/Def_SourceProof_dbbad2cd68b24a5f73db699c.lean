-- Prove2me | Definitions.Def_SourceProof_dbbad2cd68b24a5f73db699c
-- name    : SourceProof_dbbad2cd68b24a5f73db699c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:18.300016+00:00
-- url     : https://prove2.me/theorems/a40eb24b-6a2a-57b8-8682-8ef6cb471217
-- title:
--   StochLean source theorem: StochLean.TimePartition.sum_abs_increment_le

import Definitions.Def_StochLean_Analysis_PathVariation_Oscillation_F000
import Definitions.Def_SourceProof_fa85a2801ff0bffcd023f5a0
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous paths of bounded variation have zero increment quadratic variation -/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology BigOperators

namespace StochLean

variable {T : ℝ≥0}

namespace TimePartition
theorem _root_.Prove2MeSourceProof.h_dbbad2cd68b24a5f73db699c (π : TimePartition T) {f : ℝ≥0 → ℝ}
    (hf : BoundedVariationOn f (Icc 0 T)) :
    (∑ i, |π.increment f i|) ≤ (eVariationOn f (Icc 0 T)).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hf).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ abs_nonneg _)]
  exact (_root_.Prove2MeSourceProof.h_fa85a2801ff0bffcd023f5a0 π) f
end TimePartition

end StochLean


