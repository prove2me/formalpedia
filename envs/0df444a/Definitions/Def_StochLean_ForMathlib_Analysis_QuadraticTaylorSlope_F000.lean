-- Prove2me | Definitions.Def_StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000
-- name    : StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T15:01:57.632784+00:00
-- url     : https://prove2.me/theorems/10cb73e8-c614-469d-b8c1-b0a674184dfd
-- title:
--   StochLean: ForMathlib.Analysis.QuadraticTaylorSlope F000

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Order.Basic

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

noncomputable def quadraticTaylorSlope (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a = b then deriv (deriv f) a / 2 else
    (f b - f a - deriv f a * (b - a)) / (b - a) ^ 2
end StochLean


