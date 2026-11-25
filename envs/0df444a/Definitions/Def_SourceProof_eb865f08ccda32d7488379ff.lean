-- Prove2me | Definitions.Def_SourceProof_eb865f08ccda32d7488379ff
-- name    : SourceProof_eb865f08ccda32d7488379ff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:22:42.772662+00:00
-- url     : https://prove2.me/theorems/cbdf7d11-6df5-4e8e-83f2-65e13e8b21f1
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.norm_integral_le_variation_of_coefficients

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Normalization_F000
import Definitions.Def_SourceProof_dbbad2cd68b24a5f73db699c
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UniformSpace.HeineCantor

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

theorem _root_.Prove2MeSourceProof.h_eb865f08ccda32d7488379ff (H : SimplePredictableRep F)
    {C : ℝ} (hC : 0 ≤ C) (hi : ∀ ω, ‖H.initial ω‖ ≤ C)
    (hb : ∀ i ω, ‖H.coefficient i ω‖ ≤ C) (ω : Ω)
    (hf : BoundedVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))) :
    ‖H.integral X ω‖ ≤ C * (‖X 0 ω‖ +
      (eVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))).toReal) := by
  have hsum : (∑ i : Fin H.partition.size,
      ‖X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω‖) ≤
      (eVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))).toReal := by
    exact (_root_.Prove2MeSourceProof.h_dbbad2cd68b24a5f73db699c (H.partition.path ω)) hf
  unfold ProbabilityTheory.SimplePredictableRep.integral
  calc
    _ ≤ ‖H.initial ω * X 0 ω‖ +
        ‖∑ i, H.coefficient i ω *
          (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω)‖ :=
      norm_add_le _ _
    _ ≤ C * ‖X 0 ω‖ + ∑ i : Fin H.partition.size, C *
        ‖X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω‖ := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hi ω) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb i ω) (norm_nonneg _)
    _ ≤ C * ‖X 0 ω‖ + C *
        (eVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))).toReal := by
      rw [← mul_sum]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsum hC)
    _ = _ := (mul_add _ _ _).symm
end ProbabilityTheory.SimplePredictableRep


