-- Prove2me | Definitions.Def_SourceProof_f5e68e551f95dbde3aa7e530
-- name    : SourceProof_f5e68e551f95dbde3aa7e530
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:18.925965+00:00
-- url     : https://prove2.me/theorems/f9ea9089-772b-4824-af1e-e94f38db316d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsGoodIntegrator.indicator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_91776c6d66e3ec9a393c48f3
import Definitions.Def_SourceProof_e62e235b33c1e53765d13c17
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial-event masks preserve source semimartingales

The good-integrator estimate is a direct outer-measure contraction. Adaptedness
uses only measurability of the event at time zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsGoodIntegrator
theorem _root_.Prove2MeSourceProof.h_f5e68e551f95dbde3aa7e530 (hX : IsGoodIntegrator X F P) (s : Set Ω) :
    IsGoodIntegrator (fun t ↦ s.indicator (X t)) F P := by
  apply _root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mpr
  intro ε hε η hη
  obtain ⟨δ, hδ, hb⟩ := _root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mp hX ε hε η hη
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  apply le_trans (measure_mono ?_) (hb H hH hbound)
  intro ω hω
  rw [(_root_.Prove2MeSourceProof.h_e62e235b33c1e53765d13c17 hH) X s] at hω
  change ε ≤ ‖s.indicator (hH.elementaryIntegral X) ω‖ at hω
  change ε ≤ ‖hH.elementaryIntegral X ω‖
  by_cases hs : ω ∈ s
  · simpa only [indicator_of_mem hs] using hω
  · simp only [indicator_of_notMem hs, norm_zero] at hω
    exact (not_le_of_gt hε hω).elim
end IsGoodIntegrator

end ProbabilityTheory


