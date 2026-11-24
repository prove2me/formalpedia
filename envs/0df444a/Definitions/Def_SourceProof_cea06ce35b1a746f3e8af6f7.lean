-- Prove2me | Definitions.Def_SourceProof_cea06ce35b1a746f3e8af6f7
-- name    : SourceProof_cea06ce35b1a746f3e8af6f7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:51.599873+00:00
-- url     : https://prove2.me/theorems/a5f3ff85-082c-4540-8d5c-f1ff97d6b587
-- title:
--   StochLean source theorem: StochLean.measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_561d7fc50af0bdd1f0a29ad5
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.GiryMonad

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable families of locally finite Stieltjes measures on nonnegative time

Unlike the probability-CDF result on the real line, this result imposes no
normalization or finite total mass. Finite initial-interval restrictions suffice.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_cea06ce35b1a746f3e8af6f7
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → StieltjesFunction ℝ≥0} (T : ℝ≥0)
    (hf : ∀ t ≤ T, Measurable fun ω ↦ f ω t) :
    Measurable fun ω ↦ (f ω).measure.restrict (Iic T) := by
  let (ω : Ω) : IsFiniteMeasure ((f ω).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, _root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5]; exact ENNReal.ofReal_lt_top⟩
  apply Measurable.measure_of_isPiSystem (μ := fun ω ↦ (f ω).measure.restrict (Iic T))
    (S := range (Iic : ℝ≥0 → Set ℝ≥0))
    ((BorelSpace.measurable_eq (α := ℝ≥0)).trans (borel_eq_generateFrom_Iic ℝ≥0)) isPiSystem_Iic
  · rintro _ ⟨t, rfl⟩
    simp only [Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic,
      _root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5]
    exact ENNReal.measurable_ofReal.comp ((hf (min t T) (min_le_right _ _)).sub (hf 0 bot_le))
  · simp only [Measure.restrict_apply_univ, _root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5]
    exact ENNReal.measurable_ofReal.comp ((hf T le_rfl).sub (hf 0 bot_le))
end StochLean


