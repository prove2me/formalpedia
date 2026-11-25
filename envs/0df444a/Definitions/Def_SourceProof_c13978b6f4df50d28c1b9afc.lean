-- Prove2me | Definitions.Def_SourceProof_c13978b6f4df50d28c1b9afc
-- name    : SourceProof_c13978b6f4df50d28c1b9afc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:58:03.164131+00:00
-- url     : https://prove2.me/theorems/339a62b3-4846-510b-a156-e8c3996483eb
-- title:
--   StochLean source theorem: MeasureTheory.hittingAfter_lt_iff_dense_of_rightContinuous

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_8ce1e8b12b792fd0fb667ad3
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

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

theorem _root_.Prove2MeSourceProof.h_c13978b6f4df50d28c1b9afc {s : Set E} (hs : IsOpen s)
    {a T : ℝ≥0} {ω : Ω} (hX : ProbabilityTheory.IsRightContinuousPath (X · ω)) :
    hittingAfter X s a ω < T ↔
      ∃ n : ℕ, denseSeq ℝ≥0 n ∈ Ico a T ∧ X (denseSeq ℝ≥0 n) ω ∈ s := by
  rw [hittingAfter_lt_iff]
  constructor
  · rintro ⟨t, ht, hXt⟩
    exact (_root_.Prove2MeSourceProof.h_8ce1e8b12b792fd0fb667ad3 hX) hs ht.1 ht.2 hXt
  · rintro ⟨n, hn, hXn⟩
    exact ⟨denseSeq ℝ≥0 n, hn, hXn⟩
variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

end MeasureTheory


