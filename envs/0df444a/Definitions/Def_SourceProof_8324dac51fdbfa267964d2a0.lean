-- Prove2me | Definitions.Def_SourceProof_8324dac51fdbfa267964d2a0
-- name    : SourceProof_8324dac51fdbfa267964d2a0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:10:35.583795+00:00
-- url     : https://prove2.me/theorems/ce04e41f-4132-427b-a0b6-3a6b79a3d971
-- title:
--   StochLean source theorem: StochLean.exponentialJumpFactor_eq_zero_iff

import Definitions.Def_StochLean_Analysis_PathVariation_ExponentialJumpFactor_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The jump factor of the Doleans--Dade exponential

Square summability implies absolute summability of the deviations from one.
This proves convergence of the actual product, including zero and negative
factors; logarithms are not taken across those exceptional factors.
-/

@[expose] public section

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_8324dac51fdbfa267964d2a0 (u : ℝ) :
    exponentialJumpFactor u = 0 ↔ u = -1 := by
  simp only [StochLean.exponentialJumpFactor, mul_eq_zero, Real.exp_ne_zero, or_false]
  constructor <;> intro h <;> linarith
end StochLean


