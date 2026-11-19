-- Prove2me | Definitions.Def_SourceProof_5da8457f4c66732a5c2f52e6
-- name    : SourceProof_5da8457f4c66732a5c2f52e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:59:14.671616+00:00
-- url     : https://prove2.me/theorems/69a9641a-826c-44f8-93e2-671ebb9e5845
-- title:
--   LevyStochCalc source proof: LevyStochCalc.abs_sub_taylor_two_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F000

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


theorem _root_.Prove2MeSourceProof.h_5da8457f4c66732a5c2f52e6 {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|) (x y : ℝ) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ K * |y - x| ^ 3 := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hg : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt
      (fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
      (f' w - f' x - f'' x * (w - x)) (Set.uIcc x y) w := by
    intro w _
    have hA : HasDerivAt (fun z : ℝ => f z - f x) (f' w) w := (hf w).sub_const (f x)
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have hD : HasDerivAt (fun z : ℝ => (z - x) ^ 2) (2 * (w - x)) w := by
      have hmul : HasDerivAt (fun z : ℝ => (z - x) * (z - x))
          (1 * (w - x) + (w - x) * 1) w := hB.mul hB
      have hfun : (fun z : ℝ => (z - x) ^ 2) = fun z : ℝ => (z - x) * (z - x) := by
        funext z; ring
      have hval : 1 * (w - x) + (w - x) * 1 = 2 * (w - x) := by ring
      rw [hfun, ← hval]
      exact hmul
    have hE : HasDerivAt (fun z : ℝ => f'' x * (z - x) ^ 2)
        (f'' x * (2 * (w - x))) w := hD.const_mul (f'' x)
    have hF : HasDerivAt (fun z : ℝ => f'' x * (z - x) ^ 2 / 2)
        (f'' x * (2 * (w - x)) / 2) w := hE.div_const 2
    have h1 : HasDerivAt (fun z : ℝ => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
        (f' w - f' x * 1 - f'' x * (2 * (w - x)) / 2) w := (hA.sub hC).sub hF
    have h2 : f' w - f' x * 1 - f'' x * (2 * (w - x)) / 2
        = f' w - f' x - f'' x * (w - x) := by ring
    rw [h2] at h1
    exact h1.hasDerivWithinAt
  have hbound : ∀ w ∈ Set.uIcc x y,
      ‖f' w - f' x - f'' x * (w - x)‖ ≤ K * |y - x| * |y - x| := by
    intro w hw
    rw [Real.norm_eq_abs]
    refine (LevyStochCalc.abs_sub_taylor_one_le hK0 hf' hf'' x w).trans ?_
    have h1 := LevyStochCalc.abs_sub_le_of_mem_uIcc hw
    have h2 : |w - x| * |w - x| ≤ |y - x| * |y - x| :=
      mul_le_mul h1 h1 (abs_nonneg _) (abs_nonneg _)
    calc K * |w - x| * |w - x| = K * (|w - x| * |w - x|) := by ring
      _ ≤ K * (|y - x| * |y - x|) := mul_le_mul_of_nonneg_left h2 hK0
      _ = K * |y - x| * |y - x| := by ring
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hzero : f x - f x - f' x * (x - x) - f'' x * (x - x) ^ 2 / 2 = 0 := by ring
  rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmain
  calc |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2|
      ≤ K * |y - x| * |y - x| * |y - x| := hmain
    _ = K * |y - x| ^ 3 := by ring
end LevyStochCalc


