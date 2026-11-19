-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_ScaledTrig_F000
-- name    : LevyStochCalc_Analysis_ScaledTrig_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:57:10.716801+00:00
-- url     : https://prove2.me/theorems/d41c5707-bae9-4ad5-a4e2-939830f42fc3
-- title:
--   Source declarations: LevyStochCalc.Analysis.ScaledTrig
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Analysis.ScaledTrig, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The scaled cosine and sine

`x ↦ cos (l * x)` and `x ↦ sin (l * x)` are twice differentiable with derivatives bounded by
`|l|` and `l ^ 2`, and second derivatives Lipschitz with constant `|l| ^ 3` — the hypotheses of
Itô's formula for a scalar Itô process.
-/

namespace LevyStochCalc.Analysis

open Real

variable (l : ℝ)

theorem hasDerivAt_cos_scaled (x : ℝ) :
    HasDerivAt (fun y => Real.cos (l * y)) (-l * Real.sin (l * x)) x := by
  have h : HasDerivAt (fun y : ℝ => l * y) (l * 1) x := (hasDerivAt_id x).const_mul l
  have h2 := h.cos
  have heq : -Real.sin (l * x) * (l * 1) = -l * Real.sin (l * x) := by ring
  rwa [heq] at h2
theorem hasDerivAt_sin_scaled (x : ℝ) :
    HasDerivAt (fun y => Real.sin (l * y)) (l * Real.cos (l * x)) x := by
  have h : HasDerivAt (fun y : ℝ => l * y) (l * 1) x := (hasDerivAt_id x).const_mul l
  have h2 := h.sin
  have heq : Real.cos (l * x) * (l * 1) = l * Real.cos (l * x) := by ring
  rwa [heq] at h2
theorem hasDerivAt_neg_sin_scaled (x : ℝ) :
    HasDerivAt (fun y => -l * Real.sin (l * y)) (-l ^ 2 * Real.cos (l * x)) x := by
  have h := (hasDerivAt_sin_scaled l x).const_mul (-l)
  have heq : -l * (l * Real.cos (l * x)) = -l ^ 2 * Real.cos (l * x) := by ring
  rwa [heq] at h
theorem hasDerivAt_cos_scaled_mul (x : ℝ) :
    HasDerivAt (fun y => l * Real.cos (l * y)) (-l ^ 2 * Real.sin (l * x)) x := by
  have h := (hasDerivAt_cos_scaled l x).const_mul l
  have heq : l * (-l * Real.sin (l * x)) = -l ^ 2 * Real.sin (l * x) := by ring
  rwa [heq] at h
theorem abs_neg_mul_sin_scaled_le (x : ℝ) : |-l * Real.sin (l * x)| ≤ |l| := by
  rw [abs_mul, abs_neg]
  calc |l| * |Real.sin (l * x)| ≤ |l| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg l)
    _ = |l| := mul_one _
theorem abs_mul_cos_scaled_le (x : ℝ) : |l * Real.cos (l * x)| ≤ |l| := by
  rw [abs_mul]
  calc |l| * |Real.cos (l * x)| ≤ |l| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg l)
    _ = |l| := mul_one _
theorem abs_neg_sq_mul_cos_scaled_le (x : ℝ) : |-l ^ 2 * Real.cos (l * x)| ≤ l ^ 2 := by
  rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg l)]
  calc l ^ 2 * |Real.cos (l * x)| ≤ l ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg l)
    _ = l ^ 2 := mul_one _
theorem abs_neg_sq_mul_sin_scaled_le (x : ℝ) : |-l ^ 2 * Real.sin (l * x)| ≤ l ^ 2 := by
  rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg l)]
  calc l ^ 2 * |Real.sin (l * x)| ≤ l ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (sq_nonneg l)
    _ = l ^ 2 := mul_one _
end LevyStochCalc.Analysis


