-- Prove2me | Definitions.Def_SourceProof_8ce1e8b12b792fd0fb667ad3
-- name    : SourceProof_8ce1e8b12b792fd0fb667ad3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:07.27699+00:00
-- url     : https://prove2.me/theorems/a06617fb-c161-4ea9-b7a0-1429268680e5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsRightContinuousPath.exists_dense_hit_before

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Open-set hitting times for right-continuous processes

The owner is Mathlib's `hittingAfter`. Open hits strictly before a deterministic time
are detected on a fixed countable dense grid. Right continuity of the filtration then
gives the stopping-time property. At a finite hit the path belongs to the closure of
the target, not necessarily the open target itself.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E]

namespace IsRightContinuousPath
theorem _root_.Prove2MeSourceProof.h_8ce1e8b12b792fd0fb667ad3 {x : ℝ≥0 → E}
    (hx : IsRightContinuousPath x) {s : Set E} (hs : IsOpen s)
    {a t T : ℝ≥0} (hat : a ≤ t) (htT : t < T) (hxt : x t ∈ s) :
    ∃ n : ℕ, denseSeq ℝ≥0 n ∈ Ico a T ∧ x (denseSeq ℝ≥0 n) ∈ s := by
  have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
  obtain ⟨u, _, hu, hlim⟩ := hD.exists_seq_strictAnti_tendsto_of_lt htT
  have hwithin : Tendsto u atTop (𝓝[≥] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ (hu n).1.1.le⟩
  have hxu : Tendsto (fun n ↦ x (u n)) atTop (𝓝 (x t)) := (hx t).tendsto.comp hwithin
  have hmem : ∀ᶠ n in atTop, x (u n) ∈ s := hxu (hs.mem_nhds hxt)
  obtain ⟨n, hn⟩ := hmem.exists
  obtain ⟨k, hk⟩ := (hu n).2
  refine ⟨k, ?_⟩
  rw [hk]
  exact ⟨⟨hat.trans (hu n).1.1.le, (hu n).1.2⟩, hn⟩
end IsRightContinuousPath

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

end MeasureTheory


