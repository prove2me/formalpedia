-- Prove2me | solution 1 for Auto.aux_diagonal_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:42:04.986992+00:00
-- url     : https://prove2.me/submissions/49a3dada-a8b7-44af-8c11-e231bdcb2a17

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {κ : Finset ℤ} (c : Fin J → ℤ)
    (hc : ∀ j, c j ∈ κ) (F : ℤ → Fin J → ℝ≥0∞) :
    ∑ j, F (c j) j ≤ ∑ k ∈ κ, ∑ j, F k j := by
  calc
    ∑ j, F (c j) j ≤ ∑ j, ∑ k ∈ κ, F k j := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.single_le_sum (f := fun k ↦ F k j) (fun _ _ ↦ by positivity) (hc j)
    _ = ∑ k ∈ κ, ∑ j, F k j := by
      rw [Finset.sum_comm]
end Auto
