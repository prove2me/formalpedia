-- Prove2me | Definitions.Def_SourceProof_93c9621d1627047440d7fc6f
-- name    : SourceProof_93c9621d1627047440d7fc6f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:03.627488+00:00
-- url     : https://prove2.me/theorems/4200d752-79ce-5758-a9ae-e4676cbc6d2e
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurableSet_hittingAfter_lt_of_isOpen

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_c13978b6f4df50d28c1b9afc
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

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_93c9621d1627047440d7fc6f (hX : Adapted F X)
    (hr : ∀ ω, ProbabilityTheory.IsRightContinuousPath (X · ω))
    {s : Set E} (hs : IsOpen s) (a T : ℝ≥0) :
    MeasurableSet[F T] {ω | hittingAfter X s a ω < T} := by
  have heq : {ω | hittingAfter X s a ω < T} =
      ⋃ n : ℕ, ⋃ (_ : denseSeq ℝ≥0 n ∈ Ico a T), (X (denseSeq ℝ≥0 n)) ⁻¹' s := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage,
      _root_.Prove2MeSourceProof.h_c13978b6f4df50d28c1b9afc hs (hr ω), exists_prop]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro hn
  exact ((hX _).mono (F.mono hn.2.le) le_rfl) hs.measurableSet
end Adapted

end MeasureTheory


