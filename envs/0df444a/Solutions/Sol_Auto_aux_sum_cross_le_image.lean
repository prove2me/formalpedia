-- Prove2me | solution 1 for Auto.aux_sum_cross_le_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:02.142985+00:00
-- url     : https://prove2.me/submissions/4ba7e649-f7eb-4a92-82a6-2e4cd5f5a410

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_crossIndices_b_injective

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
    (hle : ∀ j ∈ aux_crossIndices b, q j ≤ V (b j.castSucc)) :
    ∑ j, q j ≤ ∑ k ∈ (aux_crossIndices b).image (fun j ↦ b j.castSucc), V k := by
  let S := aux_crossIndices b
  calc
    ∑ j, q j = ∑ j ∈ S, q j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      exact hsupport j hj
    _ ≤ ∑ j ∈ S, V (b j.castSucc) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hle j hj
    _ = ∑ k ∈ S.image (fun j ↦ b j.castSucc), V k := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      have hsub : (⟨x, hx⟩ : S) = ⟨y, hy⟩ := aux_crossIndices_b_injective hb hxy
      exact congrArg Subtype.val hsub
end Auto
