-- Prove2me | Definitions.Def_SourceProof_1217de95d74e06768f3e53ec
-- name    : SourceProof_1217de95d74e06768f3e53ec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:04.18621+00:00
-- url     : https://prove2.me/theorems/3c670d01-a862-49e7-9e09-2389d03e3d57
-- title:
--   StochLean source theorem: ProbabilityTheory.le_of_denseTimeUpTo_le_of_leftContinuous

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_a307e422895411519841ce97

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Compact deviations for left-continuous paths

The initial value is included separately from the dense grid. Left continuity
on a half-line imposes no relation between that value and its right limit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_1217de95d74e06768f3e53ec {E : Type*}
    [TopologicalSpace E] [Preorder E] [OrderClosedTopology E]
    {f : ℝ≥0 → E} (hf : IsLeftContinuousPath f) {T t : ℝ≥0} (ht : t ≤ T)
    {a : E} (hzero : f 0 ≤ a) (hbound : ∀ n, f (denseTimeUpTo T n) ≤ a) : f t ≤ a := by
  by_cases ht0 : t = 0
  · simpa only [ht0] using hzero
  have hdense : Dense (range (TopologicalSpace.denseSeq ℝ≥0)) :=
    TopologicalSpace.denseRange_denseSeq ℝ≥0
  obtain ⟨u, _, hu, hlim⟩ := hdense.exists_seq_strictMono_tendsto_of_lt
    (pos_iff_ne_zero.mpr ht0)
  have hwithin : Tendsto u atTop (𝓝[≤] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n ↦ (hu n).1.2.le⟩
  apply le_of_tendsto' ((hf t).tendsto.comp hwithin)
  intro n
  obtain ⟨k, hk⟩ := (hu n).2
  have hclip : ProbabilityTheory.denseTimeUpTo T k = u n := by
    rw [ProbabilityTheory.denseTimeUpTo, hk, min_eq_right ((hu n).1.2.le.trans ht)]
  simpa only [hclip, Function.comp_apply] using hbound k
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

end ProbabilityTheory


