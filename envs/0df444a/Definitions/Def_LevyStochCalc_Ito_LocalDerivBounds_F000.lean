-- Prove2me | Definitions.Def_LevyStochCalc_Ito_LocalDerivBounds_F000
-- name    : LevyStochCalc_Ito_LocalDerivBounds_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:55:26.592731+00:00
-- url     : https://prove2.me/theorems/fa159b01-ec97-436c-87bf-5fbe77ce8a2b
-- title:
--   Source declarations: LevyStochCalc.Ito.LocalDerivBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.LocalDerivBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Local bounds on the derivatives of a `C²` state function

A `C²` function of time and state has continuous time derivative, gradient and Hessian, so on a
compact time–space box each of them is bounded. `exists_bound_on_box` packages the three bounds
as a single constant, and `exists_bound_on_box_of_le` reads it along a path confined to a ball.

These are the local replacements for the global derivative bounds of the bounded-derivative
Itô–Lévy formula: where that theorem asks `|∂ₜu| ≤ K₀`, `|∇u| ≤ K₁` and `|∇²u| ≤ K₂` everywhere,
a path stopped on leaving a ball only meets the state function on a compact box, where the same
bounds hold for free.

## Main statements

* `exists_bound_on_box` — on `[a, b] × closedBall 0 R` the time derivative, every gradient entry
  and every Hessian entry of a `C²` function are bounded by one constant.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Ito.JumpFormula

universe u

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The sum of the absolute values of the gradient entries is continuous. -/
theorem continuous_sum_abs_gradient (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => ∑ i : Fin n, |gradient u p.1 p.2 i| :=
  continuous_finsetSum _ fun i _ => (continuous_gradient_uncurry hu i).abs
/-- The sum of the absolute values of the Hessian entries is continuous. -/
theorem continuous_sum_abs_hessian (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => ∑ i : Fin n, ∑ j : Fin n, |hessian u p.1 p.2 i j| :=
  continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (continuous_hessian hu i j).abs
end LevyStochCalc.Ito.JumpFormula


