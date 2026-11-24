-- Prove2me | Definitions.Def_SourceProof_0ed10d4235b87f87b93ee6f7
-- name    : SourceProof_0ed10d4235b87f87b93ee6f7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:14.542784+00:00
-- url     : https://prove2.me/theorems/f422da81-ea96-4ae3-b35d-5f6eb69683a4
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLeftContinuousPath.exists_dense_hit_before

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
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

namespace IsLeftContinuousPath
theorem _root_.Prove2MeSourceProof.h_0ed10d4235b87f87b93ee6f7 {x : ℝ≥0 → E}
    (hx : IsLeftContinuousPath x) {s : Set E} (hs : IsOpen s)
    {a t T : ℝ≥0} (hat : a < t) (htT : t < T) (hxt : x t ∈ s) :
    ∃ n : ℕ, denseSeq ℝ≥0 n ∈ Ioo a T ∧ x (denseSeq ℝ≥0 n) ∈ s := by
  have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
  obtain ⟨u, _, hu, hlim⟩ := hD.exists_seq_strictMono_tendsto_of_lt hat
  have hwithin : Tendsto u atTop (𝓝[≤] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ (hu n).1.2.le⟩
  have hxu : Tendsto (fun n ↦ x (u n)) atTop (𝓝 (x t)) := (hx t).tendsto.comp hwithin
  have hmem : ∀ᶠ n in atTop, x (u n) ∈ s := hxu (hs.mem_nhds hxt)
  obtain ⟨n, hn⟩ := hmem.exists
  obtain ⟨k, hk⟩ := (hu n).2
  refine ⟨k, ?_⟩
  rw [hk]
  exact ⟨⟨(hu n).1.1, (hu n).1.2.trans htT⟩, hn⟩
end IsLeftContinuousPath

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

end MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


