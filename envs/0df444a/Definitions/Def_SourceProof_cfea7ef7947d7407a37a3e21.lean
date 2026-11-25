-- Prove2me | Definitions.Def_SourceProof_cfea7ef7947d7407a37a3e21
-- name    : SourceProof_cfea7ef7947d7407a37a3e21
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:32.666367+00:00
-- url     : https://prove2.me/theorems/613fc187-aff5-5ce7-a0b8-fec6d603cf0a
-- title:
--   StochLean source theorem: MeasureTheory.eLpNorm_two_le_mul_of_integral_sq_le

import Definitions.Def_SourceProof_f17dc2585e33f77efa67337b
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Real square integrals and the extended L2 norm -/

@[expose] public section

open Filter
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {f g : Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_cfea7ef7947d7407a37a3e21 (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (C : ℝ≥0) (h : ∫ ω, (f ω) ^ 2 ∂P ≤ (C : ℝ) ^ 2 * ∫ ω, (g ω) ^ 2 ∂P) :
    eLpNorm f 2 P ≤ C * eLpNorm g 2 P := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow, _root_.Prove2MeSourceProof.h_f17dc2585e33f77efa67337b hf.integrable_sq,
    _root_.Prove2MeSourceProof.h_f17dc2585e33f77efa67337b hg.integrable_sq]
  convert ENNReal.ofReal_le_ofReal h using 1
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow C.coe_nonneg]
  simp only [ENNReal.ofReal_coe_nnreal]
end MeasureTheory


