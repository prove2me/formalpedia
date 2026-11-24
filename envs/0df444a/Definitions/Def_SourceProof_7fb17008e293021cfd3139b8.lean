-- Prove2me | Definitions.Def_SourceProof_7fb17008e293021cfd3139b8
-- name    : SourceProof_7fb17008e293021cfd3139b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:29.038806+00:00
-- url     : https://prove2.me/theorems/68985191-a032-4f40-aa0d-d0c705124303
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurableSet_hittingAfter_lt_of_leftContinuous

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_0dc1028eab53d02bbc76a512
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

/-! # Open-target hitting and exit bounds for left-continuous paths

Dense detection must include the initial time separately: a left-continuous path
on a half-line can have an isolated initial value. At a positive first exit the
norm remains bounded from above, unlike a cadlag first exit with jump overshoot.
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
theorem _root_.Prove2MeSourceProof.h_7fb17008e293021cfd3139b8 (hX : Adapted F X)
    (hl : ∀ ω, ProbabilityTheory.IsLeftContinuousPath (X · ω))
    {s : Set E} (hs : IsOpen s) (a T : ℝ≥0) :
    MeasurableSet[F T] {ω | hittingAfter X s a ω < T} := by
  have heq : {ω | hittingAfter X s a ω < T} =
      (⋃ (_ : a < T), (X a) ⁻¹' s) ∪
        ⋃ n : ℕ, ⋃ (_ : denseSeq ℝ≥0 n ∈ Ioo a T), (X (denseSeq ℝ≥0 n)) ⁻¹' s := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_preimage,
      _root_.Prove2MeSourceProof.h_0dc1028eab53d02bbc76a512 hs (hl ω), exists_prop]
  rw [heq]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro ha
    exact ((hX a).mono (F.mono ha.le) le_rfl) hs.measurableSet
  · apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro hn
    exact ((hX _).mono (F.mono hn.2.le) le_rfl) hs.measurableSet
end Adapted

end MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


