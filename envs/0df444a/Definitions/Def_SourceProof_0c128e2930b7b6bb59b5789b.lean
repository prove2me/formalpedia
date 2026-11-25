-- Prove2me | Definitions.Def_SourceProof_0c128e2930b7b6bb59b5789b
-- name    : SourceProof_0c128e2930b7b6bb59b5789b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:08.359196+00:00
-- url     : https://prove2.me/theorems/ec63446a-65fa-4bf2-9187-bc67403b64a1
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.norm_integral_min_const_le_variation

import Definitions.Def_SourceProof_8106e0a4fc271c1b04bd29a8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Pathwise variation bounds on elementary integrals

The source time-zero contribution is included separately from increment variation. Real
conversion of extended variation is used only after the corresponding finiteness proof.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_0c128e2930b7b6bb59b5789b (H : SimplePredictableRep F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) (ω : Ω) (T : ℝ≥0)
    (hf : BoundedVariationOn (fun t ↦ X t ω) (Icc 0 T)) :
    ‖H.integral (fun t ↦ X (min t T)) ω‖ ≤
      C * (‖X 0 ω‖ + (eVariationOn (fun t ↦ X t ω) (Icc 0 T)).toReal) := by
  have hv : eVariationOn (fun t ↦ X (min t T) ω) (Icc 0 (H.partition.terminal ω)) ≤
      eVariationOn (fun t ↦ X t ω) (Icc 0 T) :=
    eVariationOn.comp_le_of_monotoneOn (fun t ↦ X t ω) (fun t ↦ min t T)
      (fun _ _ _ _ h ↦ min_le_min_right _ h) (fun _ _ ↦ ⟨bot_le, min_le_right _ _⟩)
  have hfv : BoundedVariationOn (fun t ↦ X (min t T) ω) (Icc 0 (H.partition.terminal ω)) :=
    ne_top_of_le_ne_top hf hv
  have hi := (_root_.Prove2MeSourceProof.h_8106e0a4fc271c1b04bd29a8 H) hC hb ω hfv
  simp only [zero_min] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (ENNReal.toReal_mono hf hv)) hC)
end ProbabilityTheory.SimplePredictableRep


