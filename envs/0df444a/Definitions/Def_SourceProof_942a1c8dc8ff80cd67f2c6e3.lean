-- Prove2me | Definitions.Def_SourceProof_942a1c8dc8ff80cd67f2c6e3
-- name    : SourceProof_942a1c8dc8ff80cd67f2c6e3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:43.873104+00:00
-- url     : https://prove2.me/theorems/94a5e3d4-1830-4fac-b9f2-2047fa026134
-- title:
--   StochLean source theorem: StochLean.TimePartition.tendsto_rightStep_of_continuousWithinAt

import Definitions.Def_SourceProof_59527d7a236691596fcf380b
import Definitions.Def_SourceProof_5c3ed2d682980800c53cd4ac
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
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

theorem _root_.Prove2MeSourceProof.h_942a1c8dc8ff80cd67f2c6e3 {t : ℝ≥0} (ht : t ∈ Ioc 0 T)
    (hr : ContinuousWithinAt f (Ici t) t)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).taggedStep (π n).right f t) atTop (𝓝 (f t)) := by
  choose i hi using fun n ↦ (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (π n)) ht
  have hpoint : Tendsto (fun n ↦ (π n).right (i n)) atTop (𝓝[≥] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ (hi n).2⟩
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hmesh
    simpa only [dist_comm] using (_root_.Prove2MeSourceProof.h_59527d7a236691596fcf380b (π n)) (π n).right
      (fun j ↦ ⟨(_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (π n)) j, le_rfl⟩) (hi n)
  simpa only [Function.comp_def,
    fun n ↦ (_root_.Prove2MeSourceProof.h_5c3ed2d682980800c53cd4ac (π n)) (π n).right f (hi n)] using hr.tendsto.comp hpoint
end StochLean.TimePartition


