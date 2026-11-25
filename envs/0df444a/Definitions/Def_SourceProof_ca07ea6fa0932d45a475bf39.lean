-- Prove2me | Definitions.Def_SourceProof_ca07ea6fa0932d45a475bf39
-- name    : SourceProof_ca07ea6fa0932d45a475bf39
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:40:57.50858+00:00
-- url     : https://prove2.me/theorems/c6b45b05-0a48-4802-ba6e-fc7c8383bd58
-- title:
--   StochLean source theorem: StochLean.summable_abs_pair_weighted_sq_jumps

import Definitions.Def_StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000
import Definitions.Def_SourceProof_c7bae6a0333a76e8d26a8a2d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Absolute C2 jump-remainder summability from square-summable jumps

Finite variation of the original path is not required. Compact cadlag
bounds and the actual quadratic Taylor quotient dominate each remainder
by a constant times its squared jump.
-/

@[expose] public section

open Set Function ProbabilityTheory
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_ca07ea6fa0932d45a475bf39 {x : ℝ≥0 → ℝ}
    (hx : IsCadlagPath x) {T : ℝ≥0}
    (hs : Summable (fun s : Ioc 0 T ↦ (x s - leftLim x s) ^ 2))
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2)) :
    Summable (fun s : Ioc 0 T ↦ |Φ (leftLim x s) (x s) * (x s - leftLim x s) ^ 2|) := by
  obtain ⟨C, _, hC⟩ := _root_.Prove2MeSourceProof.h_c7bae6a0333a76e8d26a8a2d hx T hΦ
  apply (hs.mul_left C).of_norm_bounded
  intro s
  simp only [Real.norm_eq_abs, abs_abs, abs_mul, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (hC s ⟨s.2.1.le, s.2.2⟩) (sq_nonneg _)
end StochLean


