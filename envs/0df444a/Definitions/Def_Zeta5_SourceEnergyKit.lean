-- Prove2me | Definitions.Def_Zeta5_SourceEnergyKit
-- name    : Zeta5_SourceEnergyKit
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T23:54:45.147982+00:00
-- url     : https://prove2.me/theorems/ddf45616-34f5-4577-873b-41553b757e66
-- title:
--   Certified lower bounds for log (artanh partial sums)
-- statement:
--   Certified rational lower bounds for logarithms: `log_ge_artanh` (partial sums of the artanh series are lower bounds for `log r`, `r ≥ 1`) and `log_ge_of_pow_two` (the same after the range reduction `log y = log (2^k y) - k log 2` using `Real.log_two_lt_d9`), together with the total-mass identity `Sρ 16 = λ`.
-- source:
--   mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Measure.lean` (`Sρ_sixteen`), `Apery/EnergyConst.lean` (`log_ge_artanh`, `log_ge_of_pow_two`).

import Mathlib
import Definitions.Def_Zeta5_SourceMeasure

/-!
# Lower bounds for `log` (certified partial sums)

Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Measure.lean, Apery/EnergyConst.lean`.
Adaptations: imports re-pointed at the platform definition modules; definitions already
published on the platform are not redeclared; `Real.arctan_le_self` (absent from the pinned
Mathlib) is replaced by the local `arctan_le_self'` from `Apery/Potential.lean`.
-/

open Finset Filter Topology Set MeasureTheory

namespace Apery

/-- The total mass of `ρ` is `λ` (Appendix A.1). -/
lemma Sρ_sixteen : Sρ 16 = lam := by
  simp [Sρ, cρ, table1, Finset.sum_Icc_succ_top]
  norm_num

/-- Lower bound for `log r`, `r ≥ 1`, by a partial sum of the artanh series. -/
lemma log_ge_artanh {r : ℝ} (hr : 1 ≤ r) (m : ℕ) :
    2 * ∑ k ∈ range m, (1 / (2 * (k : ℝ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1) ≤
      Real.log r := by
  set x : ℝ := (r - 1) / (r + 1) with hx
  have hr0 : 0 < r + 1 := by linarith
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hr0.le
  have hx1 : x < 1 := by rw [hx, div_lt_one hr0]; linarith
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hr' : (1 + x) / (1 - x) = r := by
    rw [hx]; field_simp; ring
  have hlog : Real.log (1 + x) - Real.log (1 - x) = Real.log r := by
    rw [← Real.log_div (by linarith) (by linarith), hr']
  rw [hlog] at hsum
  have key := sum_le_hasSum (range m) (fun k _ => by
    have : 0 ≤ x ^ (2 * k + 1) := pow_nonneg hx0 _
    positivity) hsum
  rw [Finset.mul_sum]
  refine le_trans (le_of_eq ?_) key
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Lower bound for `log y`, `y > 0`, after the range reduction by `2^k`. -/
lemma log_ge_of_pow_two {y : ℝ} (hy : 0 < y) (k m : ℕ) (hk : 1 ≤ 2 ^ k * y) :
    2 * ∑ j ∈ range m, (1 / (2 * (j : ℝ) + 1)) *
        ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ (2 * j + 1) - k * 0.6931471808 ≤ Real.log y := by
  have h1 := log_ge_artanh hk m
  have h2 : Real.log (2 ^ k * y) = k * Real.log 2 + Real.log y := by
    rw [Real.log_mul (by positivity) hy.ne', Real.log_pow]
  have h3 := Real.log_two_lt_d9
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left h3.le hk0]

end Apery


