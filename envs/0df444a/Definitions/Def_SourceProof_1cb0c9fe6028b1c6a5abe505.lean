-- Prove2me | Definitions.Def_SourceProof_1cb0c9fe6028b1c6a5abe505
-- name    : SourceProof_1cb0c9fe6028b1c6a5abe505
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:47.265769+00:00
-- url     : https://prove2.me/theorems/e9da3fed-9aea-441e-bd2f-297c3f7d07fc
-- title:
--   StochLean source theorem: MeasureTheory.integral_sq_le_of_eLpNorm_two_le

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

theorem _root_.Prove2MeSourceProof.h_1cb0c9fe6028b1c6a5abe505 (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (h : eLpNorm f 2 P ≤ eLpNorm g 2 P) :
    ∫ ω, (f ω) ^ 2 ∂P ≤ ∫ ω, (g ω) ^ 2 ∂P := by
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun ω ↦ sq_nonneg (g ω)))).mp
  rw [← _root_.Prove2MeSourceProof.h_f17dc2585e33f77efa67337b hf.integrable_sq,
    ← _root_.Prove2MeSourceProof.h_f17dc2585e33f77efa67337b hg.integrable_sq]
  exact pow_le_pow_left' h 2
end MeasureTheory


