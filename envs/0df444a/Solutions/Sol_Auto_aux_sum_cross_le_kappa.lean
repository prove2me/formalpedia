-- Prove2me | solution 1 for Auto.aux_sum_cross_le_kappa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:21.741867+00:00
-- url     : https://prove2.me/submissions/c78b9cfa-788f-4ec6-821e-3cda1180d166

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_sum_cross_le_image

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {b : Fin (J + 1) → ℤ}
    (hb : Monotone b) (q : Fin J → ℝ≥0∞) (V : ℤ → ℝ≥0∞)
    (hsupport : ∀ j, j ∉ aux_crossIndices b → q j = 0)
    (hle : ∀ j ∈ aux_crossIndices b, q j ≤ V (b j.castSucc))
    (κ : Finset ℤ)
    (hκ : (aux_crossIndices b).image (fun j ↦ b j.castSucc) ⊆ κ) :
    ∑ j, q j ≤ ∑ k ∈ κ, V k := by
  exact (aux_sum_cross_le_image hb q V hsupport hle).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hκ fun _ _ _ ↦ by positivity)
end Auto
