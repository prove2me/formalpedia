-- Prove2me | Definitions.Def_SourceProof_67c89c4b8e6cc460cc70f997
-- name    : SourceProof_67c89c4b8e6cc460cc70f997
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:01:39.693197+00:00
-- url     : https://prove2.me/theorems/2f321f32-f488-43f8-9f69-5647a2a69e81
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Analysis.lipschitz_neg_sq_mul_cos_scaled
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
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

theorem _root_.Prove2MeSourceProof.h_67c89c4b8e6cc460cc70f997 (u v : ℝ) :
    |-l ^ 2 * Real.cos (l * u) - -l ^ 2 * Real.cos (l * v)| ≤ |l| ^ 3 * |u - v| := by
  have hfac : -l ^ 2 * Real.cos (l * u) - -l ^ 2 * Real.cos (l * v)
      = -l ^ 2 * (Real.cos (l * u) - Real.cos (l * v)) := by ring
  rw [hfac, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg l)]
  have hcos : |Real.cos (l * u) - Real.cos (l * v)| ≤ |l| * |u - v| := by
    refine (Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
    rw [← abs_mul]
    congr 1
    ring
  calc l ^ 2 * |Real.cos (l * u) - Real.cos (l * v)| ≤ l ^ 2 * (|l| * |u - v|) :=
        mul_le_mul_of_nonneg_left hcos (sq_nonneg l)
    _ = |l| ^ 3 * |u - v| := by rw [← sq_abs l]; ring
end LevyStochCalc.Analysis


