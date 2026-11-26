-- Prove2me | solution 1 for Auto.aux_mem_dyadicSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:51.474493+00:00
-- url     : https://prove2.me/submissions/42df63cf-ad3e-4a83-ba5f-fc158b845537

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_dyadicIndex_spec
public import Theorems.Thm_Auto_aux_dyadicIndex_eq_of_mem

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} (t : Fin (J + 1) → ℝ)
    (ht : ∀ j, 0 < t j) (k : ℤ) :
    k ∈ aux_dyadicSet t ↔ ∃ j, (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1) := by
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨j, -, rfl⟩
    exact ⟨j, aux_dyadicIndex_spec _ (ht j)⟩
  · rintro ⟨j, hj₁, hj₂⟩
    have heq := aux_dyadicIndex_eq_of_mem (ht j) ⟨hj₁, hj₂⟩
    rw [← heq]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
end Auto
