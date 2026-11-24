-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F001
-- name    : StochLean_Probability_Process_Path_CadlagWindowOscillation_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:13.493466+00:00
-- url     : https://prove2.me/theorems/3e33f1d7-7abb-4d65-9f20-16f569567fcf
-- title:
--   StochLean: Probability.Process.Path.CadlagWindowOscillation F001

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable two-time short-window oscillations

The envelope uses two points of the existing clipped dense grid and an actual
order and strict-width guard. Countability makes it measurable. Two right-side
approximating sequences recover every strict window of a right-continuous
path; doubling a positive width also covers a closed-width window. Cadlag
compact boundedness proves finiteness before the real-valued bridge is used.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

private theorem exists_denseTimeUpTo_right_approximation {T t : ℝ≥0} (ht : t ≤ T) :
    ∃ u : ℕ → ℕ, Tendsto (fun n ↦ denseTimeUpTo T (u n)) atTop (𝓝[≥] t) := by
  have hdense : Dense (Set.range (TopologicalSpace.denseSeq ℝ≥0)) :=
    TopologicalSpace.denseRange_denseSeq ℝ≥0
  obtain ⟨v, _, hv, hlim⟩ := hdense.exists_seq_strictAnti_tendsto t
  choose u hu using fun n ↦ (hv n).2
  have he (n : ℕ) : denseTimeUpTo T (u n) = min T (v n) := by
    rw [denseTimeUpTo, hu n]
  refine ⟨u, tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩⟩
  · simpa only [he, min_eq_right ht] using
      ((show Tendsto (fun _ : ℕ ↦ T) atTop (𝓝 T) from tendsto_const_nhds).min hlim)
  · exact Eventually.of_forall fun n ↦ by
      rw [he]
      exact le_min ht (hv n).1.le
end ProbabilityTheory


