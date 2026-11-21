-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F000
-- name    : LevyStochCalc_BSDEJ_YoungLipschitz_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:26:31.944072+00:00
-- url     : https://prove2.me/theorems/020591db-f035-47c3-a581-d9256bb4d307
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.YoungLipschitz
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.YoungLipschitz. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Young and Lipschitz pointwise rate bounds for a BSDEJ generator

Pure real-variable inequalities behind the BSDEJ contraction estimate: a weighted Young
inequality (`two_mul_mul_le_young`), a three-term square bound (`sq_add_add_le_three`), a bound
of the `Fin d → ℝ` sup norm by the sum of squared coordinates (`sq_norm_pi_le_sum_sq`), their
combination into a pointwise bound on the squared increment of a Lipschitz generator
(`sq_generator_sub_le`) and on `2 * (a * Δf)` for that increment (`two_mul_mul_generator_sub_le`
and its negated-argument form `two_mul_mul_generator_sub_le'`), and the contraction threshold on
the Young weight `β = max 2 (24 * L ^ 2)` (`contraction_factor_le`).
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Contraction

/-- Weighted Young's inequality: twice a product is at most `β / 2` times the square of the
first factor plus `2 / β` times the square of the second, for any positive weight `β`. -/
theorem two_mul_mul_le_young {β : ℝ} (hβ : 0 < β) (a b : ℝ) :
    2 * (a * b) ≤ β / 2 * a ^ 2 + 2 / β * b ^ 2 := by
  have hβ' : β ≠ 0 := hβ.ne'
  have h2β : (0 : ℝ) < 2 * β := by linarith
  have key : β / 2 * a ^ 2 + 2 / β * b ^ 2 - 2 * (a * b)
      = (β * a - 2 * b) ^ 2 / (2 * β) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (β * a - 2 * b) ^ 2 / (2 * β) := div_nonneg (sq_nonneg _) h2β.le
  linarith [key, hnn]
/-- The square of a sum of three reals is at most three times the sum of their squares. -/
theorem sq_add_add_le_three (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
/-- The (sup-norm) norm on `Fin d → ℝ`, squared, is at most the sum of the squared
coordinates. -/
theorem sq_norm_pi_le_sum_sq {d : ℕ} (z : Fin d → ℝ) : ‖z‖ ^ 2 ≤ ∑ j, z j ^ 2 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt (∑ j, z j ^ 2) := Real.sqrt_nonneg _
  have hbound : ‖z‖ ≤ Real.sqrt (∑ j, z j ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg hnn]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ (Real.sqrt (∑ j, z j ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = ∑ j, z j ^ 2 := Real.sq_sqrt (by positivity)
variable {d : ℕ} {E : Type*} [MeasurableSpace E] {ν : Measure E}
variable {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

end LevyStochCalc.BSDEJ.Contraction


