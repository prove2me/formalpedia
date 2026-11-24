-- Prove2me | Definitions.Def_SourceProof_62c74d4c6782b2a3e76047aa
-- name    : SourceProof_62c74d4c6782b2a3e76047aa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:22.202994+00:00
-- url     : https://prove2.me/theorems/83077b35-9231-4021-8956-4c197dbc9ca4
-- title:
--   StochLean source theorem: StochLean.quadraticTaylorSlope_mul_sq

import Definitions.Def_StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000
import Definitions.Def_SourceProof_1cf1f1d77236c2b817d0e363

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous quadratic Taylor quotient of a real C2 function

The diagonal is filled with one half of the second derivative, not the
totalized quotient's zero value. This is the coefficient of squared increments
in the exact finite-cell Taylor identity used for Ito's formula.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_62c74d4c6782b2a3e76047aa (f : ℝ → ℝ) (a b : ℝ) :
    quadraticTaylorSlope f a b * (b - a) ^ 2 = f b - f a - deriv f a * (b - a) := by
  by_cases h : a = b
  · subst b
    simp
  · rw [StochLean.quadraticTaylorSlope, if_neg h,
      div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h)))]
end StochLean


