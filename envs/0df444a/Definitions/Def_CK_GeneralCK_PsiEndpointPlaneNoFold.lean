-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneNoFold
-- name    : CK_GeneralCK_PsiEndpointPlaneNoFold
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:08:39.525439+00:00
-- url     : https://prove2.me/theorems/86e597ce-7bd9-4047-b121-05af7c6466b9
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneNoFold` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneNoFold` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneNoFold` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneNoFold (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneNoFold.lean)

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Convert

-- ===== source module GeneralCK.PsiEndpointPlaneNoFold =====
section

/-!
# Strict Jacobian sign for the endpoint supporting plane

This formalizes the no-fold algebra in Proposition 3.4.  A polynomial
identity proves a stronger statement than excluding a zero determinant:
the determinant numerator is strictly positive wherever both logarithmic
level functions are nonnegative.  No auxiliary square root or sign choice
for the manuscript's `P,Q,t` variables is required.
-/

namespace GeneralCK.PsiEndpointPlane

open Set

def foldNumerator (A B r s : ℝ) : ℝ :=
  (1 - r ^ 2) * (1 - s ^ 2) -
    2 * (1 + r * s) * (A * r + B * s) + 4 * A * B * r * s

def linearBound1 (A B r s : ℝ) : ℝ :=
  (1 - r ^ 2) * (1 - r * s) -
    2 * A * r * (2 + s - r * s) - 2 * B * r * s * (1 + r)

def linearBound0 (A B r s : ℝ) : ℝ :=
  (1 - s ^ 2) * (1 - r * s) -
    2 * A * r * s * (1 + s) - 2 * B * s * (2 + r - r * s)

/-- Exact positive-remainder identity, independently checked against the
manuscript's definitions before the Lean replay. -/
theorem fold_positive_remainder_identity (A B r s : ℝ) :
    2 * (1 - r * s) * foldNumerator A B r s =
      (1 + r * s) *
          ((1 - s) * linearBound1 A B r s + (1 - r) * linearBound0 A B r s) +
        (1 - r) * (1 - s) * (1 - r * s) ^ 2 * (r + s) +
        8 * A * B * r * s * (1 - r * s) := by
  unfold foldNumerator linearBound1 linearBound0
  ring

theorem foldNumerator_pos_of_linearBounds {A B r s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1)
    (hL1 : 0 ≤ linearBound1 A B r s) (hL0 : 0 ≤ linearBound0 A B r s) :
    0 < foldNumerator A B r s := by
  have hr0 := hr.1
  have hs0 := hs.1
  have hr1 : 0 < 1 - r := sub_pos.mpr hr.2
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  have hrs : r * s < 1 := (mul_lt_mul_of_pos_right hr.2 hs0).trans (by simpa using hs.2)
  have hrs1 : 0 < 1 - r * s := sub_pos.mpr hrs
  have hfirst : 0 ≤ (1 + r * s) *
      ((1 - s) * linearBound1 A B r s + (1 - r) * linearBound0 A B r s) := by
    positivity
  have hmiddle : 0 < (1 - r) * (1 - s) * (1 - r * s) ^ 2 * (r + s) := by
    positivity
  have hlast : 0 ≤ 8 * A * B * r * s * (1 - r * s) := by positivity
  have hprod : 0 < 2 * (1 - r * s) * foldNumerator A B r s := by
    rw [fold_positive_remainder_identity]
    linarith
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * (1 - r * s))).mp hprod

theorem no_fold_of_linearBounds {A B r s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1)
    (hL1 : 0 ≤ linearBound1 A B r s) (hL0 : 0 ≤ linearBound0 A B r s) :
    foldNumerator A B r s ≠ 0 :=
  (foldNumerator_pos_of_linearBounds hA hB hr hs hL1 hL0).ne'

noncomputable def singularPart (r : ℝ) : ℝ := (1 - r) ^ 2 / (2 * r)

noncomputable def level1 (A B r s : ℝ) : ℝ :=
  singularPart r + A * Real.log r + (A + B) * Real.log ((1 - s) / (1 - r * s))

noncomputable def level0 (A B r s : ℝ) : ℝ :=
  singularPart s + B * Real.log s + (A + B) * Real.log ((1 - r) / (1 - r * s))

/-- The sharpened elementary logarithm bound used in the manuscript. -/
theorem log_le_twice_sub_div_add {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.log t ≤ 2 * (t - 1) / (t + 1) := by
  let x : ℝ := (1 - t) / (1 + t)
  have hden : 0 < 1 + t := by linarith
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hden.le
  have hx1 : x < 1 := (div_lt_one hden).mpr (by linarith)
  have hbound := Real.sum_range_le_log_div hx0 hx1 1
  norm_num at hbound
  have harg : (1 + x) / (1 - x) = t⁻¹ := by
    dsimp [x]
    field_simp [ht.ne']
    ring
  rw [harg, Real.log_inv] at hbound
  have hfrac : 2 * (t - 1) / (t + 1) = -2 * x := by
    dsimp [x]
    ring
  rw [hfrac]
  linarith

/-- The rational envelope of the first logarithmic level function. -/
theorem level1_le_linearBound {A B r s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1) :
    level1 A B r s ≤
      (1 - r) / (2 * r * (1 + r) * (1 - r * s)) * linearBound1 A B r s := by
  have hr0 := hr.1
  have hs0 := hs.1
  have hden : 0 < 1 - r * s := by
    have hprod := mul_lt_mul_of_pos_right hr.2 hs0
    nlinarith [hs.2]
  have hratio : 0 < (1 - s) / (1 - r * s) := div_pos (by linarith [hs.2]) hden
  have hlogr := mul_le_mul_of_nonneg_left (log_le_twice_sub_div_add hr0 hr.2.le) hA
  have hlogratio := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio)
    (add_nonneg hA hB)
  have heq : singularPart r + A * (2 * (r - 1) / (r + 1)) +
      (A + B) * ((1 - s) / (1 - r * s) - 1) =
      (1 - r) / (2 * r * (1 + r) * (1 - r * s)) * linearBound1 A B r s := by
    unfold singularPart linearBound1
    field_simp
    ring
  unfold level1
  linarith

theorem level0_le_linearBound {A B r s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1) :
    level0 A B r s ≤
      (1 - s) / (2 * s * (1 + s) * (1 - r * s)) * linearBound0 A B r s := by
  have h := level1_le_linearBound hB hA hs hr
  convert h using 1 <;> simp only [level0, level1, linearBound0, linearBound1] <;> ring

/-- Strong no-fold theorem for the actual logarithmic level functions.
It applies to every pair of nonnegative target levels. -/
theorem foldNumerator_pos_of_nonnegative_levels {A B r s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1)
    (h1 : 0 ≤ level1 A B r s) (h0 : 0 ≤ level0 A B r s) :
    0 < foldNumerator A B r s := by
  have hr0 := hr.1
  have hs0 := hs.1
  have hden : 0 < 1 - r * s := by
    have hprod := mul_lt_mul_of_pos_right hr.2 hs0
    nlinarith [hs.2]
  have hc1 : 0 < (1 - r) / (2 * r * (1 + r) * (1 - r * s)) := by
    apply div_pos (by linarith [hr.2])
    positivity
  have hc0 : 0 < (1 - s) / (2 * s * (1 + s) * (1 - r * s)) := by
    apply div_pos (by linarith [hs.2])
    positivity
  have hL1 : 0 ≤ linearBound1 A B r s := by
    have hh := h1.trans (level1_le_linearBound hA hB hr hs)
    exact (mul_nonneg_iff_of_pos_left hc1).mp hh
  have hL0 : 0 ≤ linearBound0 A B r s := by
    have hh := h0.trans (level0_le_linearBound hA hB hr hs)
    exact (mul_nonneg_iff_of_pos_left hc0).mp hh
  exact foldNumerator_pos_of_linearBounds hA hB hr hs hL1 hL0

#print axioms fold_positive_remainder_identity
#print axioms no_fold_of_linearBounds
#print axioms foldNumerator_pos_of_nonnegative_levels

end GeneralCK.PsiEndpointPlane

end


