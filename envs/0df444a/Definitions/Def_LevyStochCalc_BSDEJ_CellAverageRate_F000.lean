-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRate_F000
-- name    : LevyStochCalc_BSDEJ_CellAverageRate_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:37.003183+00:00
-- url     : https://prove2.me/theorems/7d4481d7-8229-4b87-b2f6-0265c854fa33
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.CellAverageRate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.CellAverageRate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PathRegularity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for a deterministic Lipschitz integrand

For a function `h : ℝ → ℝ` with `|h s - h t| ≤ K * |s - t|` and a strictly monotone partition
`0 = t_0 < ⋯ < t_M = T` of mesh at most `δ`, the pathwise average of `h` over the cell
`(t_n, t_{n+1}]` containing `s` differs from `h s` by at most `K * δ`, so the energy of
`h - cellTimeAverage_Z π h` over the horizon `[0, T]` is at most `(K * δ) ^ 2 * T`.

The integrand treated here is deterministic: it is the process `Z s ω i = h s`, constant in the
sample point and in the coordinate. The cell-average rate for a random integrand is a different,
genuinely stochastic statement and is not covered by anything below.
-/

open MeasureTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u

section Lipschitz

variable {K : ℝ} {h : ℝ → ℝ}

/-- A function obeying `|h s - h t| ≤ K * |s - t|` on `ℝ` has a nonnegative constant. -/
theorem nonneg_of_lipschitz_bound (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) : 0 ≤ K := by
  have h01 := hlip 0 1
  have habs : |(0 : ℝ) - 1| = 1 := by norm_num
  rw [habs, mul_one] at h01
  exact (abs_nonneg _).trans h01
/-- A function obeying `|h s - h t| ≤ K * |s - t|` on `ℝ` is continuous. -/
theorem continuous_of_lipschitz_bound (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) :
    Continuous h := by
  have hK := nonneg_of_lipschitz_bound hlip
  refine (LipschitzWith.of_dist_le_mul (K := K.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK]
  exact hlip x y
/-- The average of a function obeying `|h s - h t| ≤ K * |s - t|` over `[a, b]` differs from its
value at any point of `(a, b]` by at most `K * (b - a)`. -/
theorem abs_sub_intervalAverage_le (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|)
    {a b s : ℝ} (hab : a < b) (hs : s ∈ Set.Ioc a b) :
    |h s - (1 / (b - a)) * ∫ u in Set.Icc a b, h u| ≤ K * (b - a) := by
  have hK := nonneg_of_lipschitz_bound hlip
  have hcont := continuous_of_lipschitz_bound hlip
  have hΔ : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hne : b - a ≠ 0 := ne_of_gt hΔ
  have hinv : (0 : ℝ) < 1 / (b - a) := div_pos one_pos hΔ
  have hvol : (volume (Set.Icc a b)).toReal = b - a := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal hΔ.le]
  have hint : IntegrableOn h (Set.Icc a b) volume := hcont.integrableOn_Icc
  have hcst : IntegrableOn (fun _ : ℝ => h s) (Set.Icc a b) volume :=
    continuous_const.integrableOn_Icc
  have hsplit : ∫ u in Set.Icc a b, (h s - h u) = (b - a) * h s - ∫ u in Set.Icc a b, h u := by
    rw [integral_sub hcst hint, setIntegral_const, smul_eq_mul, measureReal_def, hvol]
  have hrw : h s - (1 / (b - a)) * ∫ u in Set.Icc a b, h u
      = (1 / (b - a)) * ∫ u in Set.Icc a b, (h s - h u) := by
    rw [hsplit, mul_sub, ← mul_assoc, one_div, inv_mul_cancel₀ hne, one_mul]
  have hbd : |∫ u in Set.Icc a b, (h s - h u)| ≤ K * (b - a) * (b - a) := by
    have h1 : ‖∫ u in Set.Icc a b, (h s - h u)‖
        ≤ K * (b - a) * volume.real (Set.Icc a b) := by
      refine norm_setIntegral_le_of_norm_le_const ?_ fun u hu => ?_
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      · rw [Real.norm_eq_abs]
        refine (hlip s u).trans (mul_le_mul_of_nonneg_left ?_ hK)
        obtain ⟨hua, hub⟩ := hu
        obtain ⟨hsa, hsb⟩ := hs
        rw [abs_le]
        constructor <;> linarith
    rwa [Real.norm_eq_abs, measureReal_def, hvol] at h1
  rw [hrw, abs_mul, abs_of_pos hinv]
  calc 1 / (b - a) * |∫ u in Set.Icc a b, (h s - h u)|
      ≤ 1 / (b - a) * (K * (b - a) * (b - a)) := mul_le_mul_of_nonneg_left hbd hinv.le
    _ = K * (b - a) := by field_simp
end Lipschitz

section Cells

variable {M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}

end Cells

section Deterministic

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}

end Deterministic

end LevyStochCalc.BSDEJ.PathRegularity


