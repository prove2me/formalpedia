-- Prove2me | Definitions.Def_SourceProof_27683b508bd10711c3a5188a
-- name    : SourceProof_27683b508bd10711c3a5188a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:35:31.053479+00:00
-- url     : https://prove2.me/theorems/c740d3bf-e7ad-44d0-96d1-8e7ebdb7c5bf
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurableSet_exists_large_jump_Ioo

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_75905791bb0754da30478f5d
import Definitions.Def_SourceProof_852602f438752e1b49fad297

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

theorem _root_.Prove2MeSourceProof.h_27683b508bd10711c3a5188a (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (s t : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    MeasurableSet[F t] {ω | ∃ u : ℝ≥0, s < u ∧ u < t ∧
      b < ‖jumpProcess X u ω‖} := by
  classical
  let : MeasurableSpace Ω := F t
  have he : {ω | ∃ u : ℝ≥0, s < u ∧ u < t ∧ b < ‖ProbabilityTheory.jumpProcess X u ω‖} =
      {ω | ∃ c : ℚ, ∃ i j : ℕ,
        (b < (c : ℝ) ∧ s < denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 j < t) ∧
          ProbabilityTheory.HasArbitrarilyShortDenseIncrements (X · ω)
            (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) c} := by
    ext ω
    rw [Set.mem_ofPred_eq, (_root_.Prove2MeSourceProof.h_852602f438752e1b49fad297 (hc ω)) s t hb]
    constructor
    · rintro ⟨c, hbc, i, j, hsi, hjt, hinc⟩
      exact ⟨c, i, j, ⟨hbc, hsi, hjt⟩, hinc⟩
    · rintro ⟨c, i, j, ⟨hbc, hsi, hjt⟩, hinc⟩
      exact ⟨c, hbc, i, j, hsi, hjt, hinc⟩
  rw [he]
  simp_rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro c
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hC : b < (c : ℝ) ∧ s < denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 j < t
  · simp only [hC, true_and]
    exact (_root_.Prove2MeSourceProof.h_75905791bb0754da30478f5d hX)
      (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) t hC.2.2.le c
  · simp only [hC, false_and]
    exact MeasurableSet.empty
end Adapted

end MeasureTheory


