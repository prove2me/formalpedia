-- Prove2me | solution 1 for Auto.aux_CuboidNorm.lintegral_count_natToInt_enorm_rpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:20.476638+00:00
-- url     : https://prove2.me/submissions/5c608efb-51bc-49da-951c-d6f81831eefe

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_count_enorm_rpow_eq_finset
public import Theorems.Thm_Auto_aux_CuboidNorm_natToInt_eq_of_embedding
public import Theorems.Thm_Auto_aux_CuboidNorm_natToInt_support_map

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ}
    (A : Finset (Fin n → ℕ)) (F : (Fin n → ℕ) → ℝ)
    (hsupport : ∀ k, k ∉ A → F k = 0) (q : ℝ) (hq : 0 < q) :
    (∫⁻ z, ‖aux_natToInt F z‖ₑ ^ q ∂Measure.count) =
      ∫⁻ k, ‖F k‖ₑ ^ q ∂Measure.count := by
  rw [lintegral_count_enorm_rpow_eq_finset (A.map natToIntEmbedding)
    (aux_natToInt F) q hq (natToInt_support_map A F hsupport)]
  rw [lintegral_count_enorm_rpow_eq_finset A F q hq hsupport]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k hk
  rw [natToInt_eq_of_embedding]
end Auto.aux_CuboidNorm
