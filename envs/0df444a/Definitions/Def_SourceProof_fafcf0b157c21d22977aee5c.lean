-- Prove2me | Definitions.Def_SourceProof_fafcf0b157c21d22977aee5c
-- name    : SourceProof_fafcf0b157c21d22977aee5c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:07.25672+00:00
-- url     : https://prove2.me/theorems/86cd067c-f2c0-4601-8810-0c0baa9090b7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsGoodIntegrator.add

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_487832d6cb2410ff018577d0
import Definitions.Def_SourceProof_91776c6d66e3ec9a393c48f3
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linear stability of the source good-integrator predicate

These results use elementary integration and its quantitative continuity
criterion. No classical decomposition or Bichteler-Dellacherie theorem is
assumed in proving stability.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsGoodIntegrator
theorem _root_.Prove2MeSourceProof.h_fafcf0b157c21d22977aee5c (hX : IsGoodIntegrator X F P) (hY : IsGoodIntegrator Y F P) :
    IsGoodIntegrator (X + Y) F P := by
  apply _root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mpr
  intro ε hε η hη
  obtain ⟨δX, hδX, hXbound⟩ := (_root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mp hX)
    (ε / 2) (half_pos hε) (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨δY, hδY, hYbound⟩ := (_root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mp hY)
    (ε / 2) (half_pos hε) (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨min δX δY, lt_min hδX hδY, ?_⟩
  intro H hH hb
  have hbX := hXbound H hH (fun t ω ↦ (hb t ω).trans (min_le_left _ _))
  have hbY := hYbound H hH (fun t ω ↦ (hb t ω).trans (min_le_right _ _))
  rw [(_root_.Prove2MeSourceProof.h_487832d6cb2410ff018577d0 hH)]
  have hs : {ω | ε ≤ ‖(hH.elementaryIntegral X + hH.elementaryIntegral Y) ω‖} ⊆
      {ω | ε / 2 ≤ ‖hH.elementaryIntegral X ω‖} ∪
        {ω | ε / 2 ≤ ‖hH.elementaryIntegral Y ω‖} := by
    intro ω hω
    by_contra h
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at h
    have hn := norm_add_le (hH.elementaryIntegral X ω) (hH.elementaryIntegral Y ω)
    change ε ≤ ‖hH.elementaryIntegral X ω + hH.elementaryIntegral Y ω‖ at hω
    linarith
  calc
    _ ≤ P ({ω | ε / 2 ≤ ‖hH.elementaryIntegral X ω‖} ∪
        {ω | ε / 2 ≤ ‖hH.elementaryIntegral Y ω‖}) := measure_mono hs
    _ ≤ _ := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hbX hbY
    _ = η := ENNReal.add_halves η
end IsGoodIntegrator

end ProbabilityTheory


