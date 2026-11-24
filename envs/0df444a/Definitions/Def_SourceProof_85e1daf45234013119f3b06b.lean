-- Prove2me | Definitions.Def_SourceProof_85e1daf45234013119f3b06b
-- name    : SourceProof_85e1daf45234013119f3b06b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:42.325223+00:00
-- url     : https://prove2.me/theorems/e008a6df-816e-4bda-b879-4fc9b03805d8
-- title:
--   StochLean source theorem: MeasureTheory.eLpNorm_two_eq_ofReal_integral_sq_rpow

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

theorem _root_.Prove2MeSourceProof.h_85e1daf45234013119f3b06b (hf : Integrable (fun ω ↦ (f ω) ^ 2) P) :
    eLpNorm f 2 P = ENNReal.ofReal (∫ ω, (f ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  rw [show eLpNorm f 2 P =
      (∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂P) ^ (1 / 2 : ℝ) by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
    congr 2
    funext ω
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]]
  rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun ω ↦ sq_nonneg (f ω))]
end MeasureTheory


