-- Prove2me | Definitions.Def_SourceProof_f17dc2585e33f77efa67337b
-- name    : SourceProof_f17dc2585e33f77efa67337b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:27.455287+00:00
-- url     : https://prove2.me/theorems/ea8e9e3b-1d7f-42bf-9cf5-ab1e5f1dc0f0
-- title:
--   StochLean source theorem: MeasureTheory.sq_eLpNorm_two_eq_ofReal_integral_sq

import Definitions.Def_SourceProof_85e1daf45234013119f3b06b

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

theorem _root_.Prove2MeSourceProof.h_f17dc2585e33f77efa67337b (hf : Integrable (fun ω ↦ (f ω) ^ 2) P) :
    (eLpNorm f 2 P) ^ 2 = ENNReal.ofReal (∫ ω, (f ω) ^ 2 ∂P) := by
  rw [_root_.Prove2MeSourceProof.h_85e1daf45234013119f3b06b hf, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
end MeasureTheory


