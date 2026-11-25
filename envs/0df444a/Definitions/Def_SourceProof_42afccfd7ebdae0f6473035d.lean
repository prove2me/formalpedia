-- Prove2me | Definitions.Def_SourceProof_42afccfd7ebdae0f6473035d
-- name    : SourceProof_42afccfd7ebdae0f6473035d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:32.083858+00:00
-- url     : https://prove2.me/theorems/06c43ba8-46b5-4a03-a366-285344c785c1
-- title:
--   StochLean source theorem: ProbabilityTheory.isGoodIntegrator_of_eq_off_small_sets

import Definitions.Def_SourceProof_1c5b3fc9d4606b838c65c75d
import Definitions.Def_SourceProof_91776c6d66e3ec9a393c48f3

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Localization of source good integrators and semimartingales

Elementary integrals agree when entire integrator paths agree. This proves closure under
approximation outside sets of vanishing probability and then the local-to-global direction
for ordinary semimartingales, including the Protter time-zero mask.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_42afccfd7ebdae0f6473035d (Y : ℕ → ℝ≥0 → Ω → ℝ) (E : ℕ → Set Ω)
    (hY : ∀ n, IsGoodIntegrator (Y n) F P)
    (heq : ∀ n ω, ω ∉ E n → ∀ t, X t ω = Y n t ω)
    (hsmall : Tendsto (fun n ↦ P (E n)) atTop (𝓝 0)) : IsGoodIntegrator X F P := by
  apply _root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mpr
  intro ε hε η hη
  obtain ⟨n, hn⟩ := (hsmall.eventually_lt_const (ENNReal.half_pos hη.ne')).exists
  obtain ⟨δ, hδ, hb⟩ := (_root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mp (hY n))
    ε hε (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  have hs : {ω | ε ≤ ‖hH.elementaryIntegral X ω‖} ⊆
      E n ∪ {ω | ε ≤ ‖hH.elementaryIntegral (Y n) ω‖} := by
    intro ω hω
    by_cases hE : ω ∈ E n
    · exact Or.inl hE
    · exact Or.inr (by
        change ε ≤ ‖hH.elementaryIntegral (Y n) ω‖
        rw [← (_root_.Prove2MeSourceProof.h_1c5b3fc9d4606b838c65c75d hH) (heq n ω hE)]
        exact hω)
  calc
    _ ≤ P (E n ∪ {ω | ε ≤ ‖hH.elementaryIntegral (Y n) ω‖}) := measure_mono hs
    _ ≤ P (E n) + P {ω | ε ≤ ‖hH.elementaryIntegral (Y n) ω‖} := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hn.le (hb H hH hbound)
    _ = η := ENNReal.add_halves η
variable [IsFiniteMeasure P]

end ProbabilityTheory


