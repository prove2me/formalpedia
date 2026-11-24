-- Prove2me | Definitions.Def_SourceProof_1cf1f1d77236c2b817d0e363
-- name    : SourceProof_1cf1f1d77236c2b817d0e363
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:12:49.502033+00:00
-- url     : https://prove2.me/theorems/06cd985c-9321-4398-8383-69ec6501a8c6
-- title:
--   StochLean source theorem: StochLean.quadraticTaylorSlope_self

import Definitions.Def_StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000

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

@[simp] theorem _root_.Prove2MeSourceProof.h_1cf1f1d77236c2b817d0e363 (f : ℝ → ℝ) (a : ℝ) :
    quadraticTaylorSlope f a a = deriv (deriv f) a / 2 := by
  simp only [StochLean.quadraticTaylorSlope, ↓reduceIte]
end StochLean


