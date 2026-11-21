-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoTruncate_F000
-- name    : LevyStochCalc_Brownian_ItoTruncate_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:42:51.46193+00:00
-- url     : https://prove2.me/theorems/b428472c-955c-4b13-aa49-637abe6cd12d
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoTruncate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoTruncate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoVersionExists_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating an integrand to a bounded one

Clamping a real integrand to `[-j, j]` leaves a bounded integrand that approximates it in energy:
the clamp is `1`-Lipschitz, fixes `0`, never increases the absolute value, and converges to the
identity pointwise, so dominated convergence gives energy convergence on every window.

## Main statements

* `LevyStochCalc.clampAt` — the clamp.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub` — the clamped integrand converges to
  the integrand in energy.
-/

namespace LevyStochCalc

open MeasureTheory
open scoped NNReal ENNReal Topology

section Clamp

/-- The clamp of a real number to `[-j, j]`. -/
noncomputable def clampAt (j x : ℝ) : ℝ := max (-j) (min j x)
theorem clampAt_zero {j : ℝ} (hj : 0 ≤ j) : clampAt j 0 = 0 := by
  unfold clampAt
  rw [min_eq_right hj, max_eq_right (by linarith : -j ≤ (0 : ℝ))]
theorem continuous_clampAt (j : ℝ) : Continuous (clampAt j) := by
  unfold clampAt
  fun_prop
theorem abs_clampAt_le {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x| ≤ j := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx, abs_neg, abs_of_nonneg hj]
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le, abs_le]
      exact ⟨hx.le, hx'⟩
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j), abs_of_nonneg hj]
theorem abs_clampAt_le_abs {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x| ≤ |x| := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx, abs_neg, abs_of_nonneg hj,
      abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le]
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j), abs_of_nonneg hj,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      linarith
theorem abs_clampAt_sub_le {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x - x| ≤ |x| := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ -j - x), abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le]
      simp
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j),
        abs_of_nonpos (by linarith : j - x ≤ 0), abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      linarith
theorem clampAt_eq_self {j x : ℝ} (hx : |x| ≤ j) : clampAt j x = x := by
  rw [abs_le] at hx
  unfold clampAt
  rw [min_eq_right hx.2, max_eq_right hx.1]
theorem tendsto_clampAt (x : ℝ) :
    Filter.Tendsto (fun j : ℕ => clampAt (j : ℝ) x) Filter.atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop N] with j hj
  refine (clampAt_eq_self ?_).symm
  exact hN.le.trans (by exact_mod_cast hj)
end Clamp

namespace Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem eventually_clampAt_eq (x : ℝ) : ∀ᶠ j : ℕ in Filter.atTop, clampAt (j : ℝ) x = x := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  filter_upwards [Filter.eventually_ge_atTop N] with j hj
  exact clampAt_eq_self (hN.le.trans (by exact_mod_cast hj))
section Difference

open LevyStochCalc.Brownian.Multidim

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

end Difference

end Brownian.Ito

end LevyStochCalc


