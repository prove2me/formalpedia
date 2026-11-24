-- Prove2me | Definitions.Def_SourceProof_75905791bb0754da30478f5d
-- name    : SourceProof_75905791bb0754da30478f5d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:24.429894+00:00
-- url     : https://prove2.me/theorems/5960b6d3-10d0-485e-bcfc-3d20686ce48c
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurableSet_arbitrarilyShortDenseIncrements

import Definitions.Def_StochLean_Probability_Process_Path_CadlagLargeJumpDetection_F000
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable occurrence of a large cadlag jump

Only adapted coordinates at times below the fixed right endpoint are used.
The deterministic dense-increment characterization replaces an uncountable
projection by countable unions and intersections. Everywhere cadlag paths
suffice; neither completeness nor right continuity of the filtration is
required for these fixed-horizon occurrence events.
-/

@[expose] public section

open ProbabilityTheory Set TopologicalSpace
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_75905791bb0754da30478f5d (hX : Adapted F X)
    (a d t : ℝ≥0) (hdt : d ≤ t) (c : ℝ) :
    MeasurableSet[F t] {ω | HasArbitrarilyShortDenseIncrements (X · ω) a d c} := by
  classical
  let : MeasurableSpace Ω := F t
  unfold ProbabilityTheory.HasArbitrarilyShortDenseIncrements
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  simp_rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hC : a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧
      denseSeq ℝ≥0 j ≤ d ∧
        dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < 1 / (n + 1 : ℝ)
  · have he : {ω | a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧
        denseSeq ℝ≥0 j ≤ d ∧
          dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < 1 / (n + 1 : ℝ) ∧
            c < ‖X (denseSeq ℝ≥0 j) ω - X (denseSeq ℝ≥0 i) ω‖} =
        {ω | c < ‖X (denseSeq ℝ≥0 j) ω - X (denseSeq ℝ≥0 i) ω‖} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      tauto
    rw [he]
    have hi := (hX (denseSeq ℝ≥0 i)).mono
      (F.mono (hC.2.1.trans (hC.2.2.1.trans hdt))) le_rfl
    have hj := (hX (denseSeq ℝ≥0 j)).mono (F.mono (hC.2.2.1.trans hdt)) le_rfl
    exact measurableSet_lt measurable_const (hj.sub hi).norm
  · have he : {ω | a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧
        denseSeq ℝ≥0 j ≤ d ∧
          dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < 1 / (n + 1 : ℝ) ∧
            c < ‖X (denseSeq ℝ≥0 j) ω - X (denseSeq ℝ≥0 i) ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      tauto
    rw [he]
    exact MeasurableSet.empty
end Adapted

end MeasureTheory


