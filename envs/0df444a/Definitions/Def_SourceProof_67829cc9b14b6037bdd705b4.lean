-- Prove2me | Definitions.Def_SourceProof_67829cc9b14b6037bdd705b4
-- name    : SourceProof_67829cc9b14b6037bdd705b4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:01:30.872854+00:00
-- url     : https://prove2.me/theorems/6d135e76-d4db-430d-b4bd-28f01ea58eb9
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Analysis.lipschitz_neg_sq_mul_sin_scaled
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

theorem _root_.Prove2MeSourceProof.h_67829cc9b14b6037bdd705b4 (u v : ℝ) :
    |-l ^ 2 * Real.sin (l * u) - -l ^ 2 * Real.sin (l * v)| ≤ |l| ^ 3 * |u - v| := by
  have hfac : -l ^ 2 * Real.sin (l * u) - -l ^ 2 * Real.sin (l * v)
      = -l ^ 2 * (Real.sin (l * u) - Real.sin (l * v)) := by ring
  rw [hfac, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg l)]
  have hsin : |Real.sin (l * u) - Real.sin (l * v)| ≤ |l| * |u - v| := by
    refine (Real.abs_sin_sub_sin_le _ _).trans (le_of_eq ?_)
    rw [← abs_mul]
    congr 1
    ring
  calc l ^ 2 * |Real.sin (l * u) - Real.sin (l * v)| ≤ l ^ 2 * (|l| * |u - v|) :=
        mul_le_mul_of_nonneg_left hsin (sq_nonneg l)
    _ = |l| ^ 3 * |u - v| := by rw [← sq_abs l]; ring
end LevyStochCalc.Analysis


