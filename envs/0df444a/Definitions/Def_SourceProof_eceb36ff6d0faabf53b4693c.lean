-- Prove2me | Definitions.Def_SourceProof_eceb36ff6d0faabf53b4693c
-- name    : SourceProof_eceb36ff6d0faabf53b4693c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:42:06.730363+00:00
-- url     : https://prove2.me/theorems/397dcbf5-38a1-4004-9819-2f0b6d02541a
-- title:
--   StochLean source theorem: StochLean.TimePartition.endpointPairStep_eq_of_mem_cell

import Definitions.Def_StochLean_Analysis_PathVariation_EndpointPairStep_F000
import Definitions.Def_SourceProof_0d9d0191109103cc7be46cb1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite steps depending on both cell endpoint values

Repeated endpoints are allowed. At positive times the unique nonempty cell
determines both values; the initial value is retained separately.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

namespace TimePartition

variable {T : ℝ≥0} {E : Type*}

theorem _root_.Prove2MeSourceProof.h_eceb36ff6d0faabf53b4693c (π : TimePartition T) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) {t : ℝ≥0} {i : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) :
    π.endpointPairStep Φ x t = Φ (x (π.left i)) (x (π.right i)) := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hi.1)
  rw [StochLean.TimePartition.endpointPairStep, if_neg ht, Finset.sum_eq_single i]
  · exact indicator_of_mem (s := Ioc (π.left i) (π.right i)) (a := t) hi _
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact hji ((_root_.Prove2MeSourceProof.h_0d9d0191109103cc7be46cb1 π) hj hi)
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
end TimePartition

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

end StochLean


