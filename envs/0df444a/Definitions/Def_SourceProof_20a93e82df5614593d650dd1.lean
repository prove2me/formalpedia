-- Prove2me | Definitions.Def_SourceProof_20a93e82df5614593d650dd1
-- name    : SourceProof_20a93e82df5614593d650dd1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:08:01.578005+00:00
-- url     : https://prove2.me/theorems/f3c6c1b0-a263-448c-ad73-c9d431f80629
-- title:
--   StochLean source theorem: MeasureTheory.measure_norm_ge_le_integral_sq_div

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

theorem _root_.Prove2MeSourceProof.h_20a93e82df5614593d650dd1 [IsFiniteMeasure P]
    (hf : Integrable (fun ω ↦ (f ω) ^ 2) P) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ ‖f ω‖} ≤ ENNReal.ofReal ((∫ ω, (f ω) ^ 2 ∂P) / ε ^ 2) := by
  have hs : {ω | ε ^ 2 ≤ (f ω) ^ 2} = {ω | ε ≤ ‖f ω‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, ← sq_abs (f ω)]
    exact sq_le_sq₀ hε.le (abs_nonneg _)
  have h := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all P (fun ω ↦ sq_nonneg (f ω))) hf (ε ^ 2)
  rw [hs] at h
  have hb : P.real {ω | ε ≤ ‖f ω‖} ≤ (∫ ω, (f ω) ^ 2 ∂P) / ε ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by simpa only [mul_comm] using h)
  calc
    _ = ENNReal.ofReal (P.real {ω | ε ≤ ‖f ω‖}) :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb
end MeasureTheory


