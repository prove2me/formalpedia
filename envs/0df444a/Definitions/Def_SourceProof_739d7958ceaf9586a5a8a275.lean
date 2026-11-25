-- Prove2me | Definitions.Def_SourceProof_739d7958ceaf9586a5a8a275
-- name    : SourceProof_739d7958ceaf9586a5a8a275
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:04.848223+00:00
-- url     : https://prove2.me/theorems/b0104519-2f8c-488b-9017-d009b1fc5e5c
-- title:
--   StochLean source theorem: StochLean.TimePartition.tendsto_leftStep_of_tendsto_left

import Definitions.Def_StochLean_Analysis_PathVariation_TaggedStepApproximation_F000
import Definitions.Def_SourceProof_1f1a39edad68d4f3bc6e94ca
import Definitions.Def_SourceProof_7ebcdf415b376e81ffc593ac
import Definitions.Def_SourceProof_8f7895612117943074291d58
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

theorem _root_.Prove2MeSourceProof.h_739d7958ceaf9586a5a8a275 {t : ℝ≥0} (ht : t ∈ Ioc 0 T) {l : ℝ}
    (hl : Tendsto f (𝓝[<] t) (𝓝 l))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).leftStep f t) atTop (𝓝 l) := by
  choose i hi using fun n ↦ (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (π n)) ht
  have hpoint : Tendsto (fun n ↦ (π n).left (i n)) atTop (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ (hi n).1⟩
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hmesh
    simpa only [dist_comm] using (_root_.Prove2MeSourceProof.h_7ebcdf415b376e81ffc593ac (π n)) (hi n)
  simpa only [Function.comp_def, fun n ↦ (_root_.Prove2MeSourceProof.h_1f1a39edad68d4f3bc6e94ca (π n)) f (hi n)] using
    hl.comp hpoint
end StochLean.TimePartition


