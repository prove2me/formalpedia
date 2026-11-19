-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F000
-- name    : LevyStochCalc_Brownian_TaylorTwo_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:58:47.343844+00:00
-- url     : https://prove2.me/theorems/999c9052-1dcb-4c01-9ce1-e062fe8907fa
-- title:
--   Source declarations: LevyStochCalc.Brownian.TaylorTwo
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Brownian.TaylorTwo, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.Calculus.MeanValue

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second-order Taylor bound with a Lipschitz second derivative

For a twice-differentiable real function whose second derivative is `K`-Lipschitz, the
second-order Taylor polynomial approximates the function to within `K|y − x|³`.

## Main statements

* `LevyStochCalc.abs_sub_taylor_one_le` — the first-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_taylor_two_le` — the second-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_sum_taylor_two_le` — the telescoped form along a sequence.
* `LevyStochCalc.taylorRemainder` — the telescoped remainder as a function of the sequence.
* `LevyStochCalc.abs_taylorRemainder_le` — its bound.
-/

namespace LevyStochCalc

/-- On the segment between `x` and `y`, no point is further from `x` than `y` is. -/
theorem abs_sub_le_of_mem_uIcc {x y w : ℝ} (hw : w ∈ Set.uIcc x y) : |w - x| ≤ |y - x| := by
  rcases Set.mem_uIcc.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - x),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    linarith
  · rw [abs_of_nonpos (by linarith : w - x ≤ 0), abs_of_nonpos (by linarith : y - x ≤ 0)]
    linarith
/-- **First-order Taylor remainder for a Lipschitz derivative.** -/
theorem abs_sub_taylor_one_le {f f' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ u v : ℝ, |f' u - f' v| ≤ K * |u - v|)
    (x y : ℝ) : |f y - f x - f' x * (y - x)| ≤ K * |y - x| * |y - x| := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hg : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt (fun z => f z - f x - f' x * (z - x))
      (f' w - f' x) (Set.uIcc x y) w := by
    intro w _
    have hA : HasDerivAt (fun z : ℝ => f z - f x) (f' w) w := (hf w).sub_const (f x)
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have h1 : HasDerivAt (fun z : ℝ => f z - f x - f' x * (z - x)) (f' w - f' x * 1) w :=
      hA.sub hC
    rw [mul_one] at h1
    exact h1.hasDerivWithinAt
  have hbound : ∀ w ∈ Set.uIcc x y, ‖f' w - f' x‖ ≤ K * |y - x| := by
    intro w hw
    rw [Real.norm_eq_abs]
    exact (hf' w x).trans (mul_le_mul_of_nonneg_left (abs_sub_le_of_mem_uIcc hw) hK0)
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmain
end LevyStochCalc


