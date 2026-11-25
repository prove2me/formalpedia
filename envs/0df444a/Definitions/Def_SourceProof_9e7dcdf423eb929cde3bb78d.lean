-- Prove2me | Definitions.Def_SourceProof_9e7dcdf423eb929cde3bb78d
-- name    : SourceProof_9e7dcdf423eb929cde3bb78d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:51.8767+00:00
-- url     : https://prove2.me/theorems/465a2ff5-c4ff-49ea-be6f-030377e86140
-- title:
--   StochLean source theorem: StochLean.TimePartition.norm_taggedStep_le

import Definitions.Def_StochLean_Analysis_PathVariation_TaggedStepApproximation_F000
import Definitions.Def_SourceProof_5c3ed2d682980800c53cd4ac
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_b7e4a2ea52c5aed858bf1da5
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint step convergence at jumps

On positive-time cells the left endpoint approaches strictly from below,
while the right endpoint approaches from above, allowing equality. Thus the
limits are different at jumps. No uniform convergence is asserted.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0} {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}

theorem _root_.Prove2MeSourceProof.h_9e7dcdf423eb929cde3bb78d (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (hξ : ∀ i, ξ i ∈ Icc 0 T) {C : ℝ} (hb : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ C)
    {t : ℝ≥0} (ht : t ∈ Icc 0 T) : ‖π.taggedStep ξ f t‖ ≤ C := by
  by_cases ht0 : t = 0
  · subst t
    rw [_root_.Prove2MeSourceProof.h_b7e4a2ea52c5aed858bf1da5]
    exact hb 0 ht
  · obtain ⟨i, hi⟩ := (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 π) ⟨pos_iff_ne_zero.mpr ht0, ht.2⟩
    rw [(_root_.Prove2MeSourceProof.h_5c3ed2d682980800c53cd4ac π) ξ f hi]
    exact hb (ξ i) (hξ i)
end StochLean.TimePartition


