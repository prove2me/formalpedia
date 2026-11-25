-- Prove2me | Definitions.Def_SourceProof_c0a1798fe7969c16cff73dff
-- name    : SourceProof_c0a1798fe7969c16cff73dff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:23.928864+00:00
-- url     : https://prove2.me/theorems/530e0555-27e6-52a9-ab7f-033a096364cc
-- title:
--   StochLean source theorem: StochLean.exists_norm_frechetTaylorErrorCoefficient_le

import Definitions.Def_StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000
import Definitions.Def_SourceProof_6c8628105866f38712113f22
import Definitions.Def_SourceProof_c000c5f373823d994f025530

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A continuous diagonal-zero coefficient for the Frechet Taylor error

Dividing the actual second-order error by the squared increment norm gives
a coefficient continuous even on the diagonal. This makes the jump-separation
argument applicable to vector paths without a discontinuous directional choice.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

theorem _root_.Prove2MeSourceProof.h_c0a1798fe7969c16cff73dff (hf : ContDiff ℝ 2 f) (a b : E) :
    ∃ θ ∈ Icc (0 : ℝ) 1, ‖frechetTaylorErrorCoefficient f a b‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (a + θ • (b - a)) - fderiv ℝ (fderiv ℝ f) a‖ / 2 := by
  obtain ⟨θ, hθ, he⟩ := _root_.Prove2MeSourceProof.h_c000c5f373823d994f025530 hf a b
  refine ⟨θ, hθ, ?_⟩
  let L := fderiv ℝ (fderiv ℝ f) (a + θ • (b - a)) - fderiv ℝ (fderiv ℝ f) a
  have hR : StochLean.frechetSecondOrderRemainder f a b = (1 / 2 : ℝ) * L (b - a) (b - a) := by
    rw [StochLean.frechetSecondOrderRemainder, he, ← mul_sub]
    rfl
  have hL : ‖L (b - a) (b - a)‖ ≤ ‖L‖ * ‖b - a‖ ^ 2 := by
    calc
      _ ≤ ‖L (b - a)‖ * ‖b - a‖ := (L (b - a)).le_opNorm _
      _ ≤ (‖L‖ * ‖b - a‖) * ‖b - a‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  by_cases h : b = a
  · subst b
    simp only [_root_.Prove2MeSourceProof.h_6c8628105866f38712113f22, norm_zero]
    positivity
  · have hn : 0 < ‖b - a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h))
    rw [StochLean.frechetTaylorErrorCoefficient, norm_div, norm_pow, norm_norm, hR, norm_mul,
      show ‖(1 / 2 : ℝ)‖ = 1 / 2 from by norm_num]
    apply (div_le_iff₀ hn).mpr
    change (1 / 2 : ℝ) * ‖L (b - a) (b - a)‖ ≤ ‖L‖ / 2 * ‖b - a‖ ^ 2
    nlinarith only [hL]
end StochLean


