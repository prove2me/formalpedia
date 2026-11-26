-- Prove2me | solution 1 for Auto.aux_CuboidNorm.natToInt_eq_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:49:17.158626+00:00
-- url     : https://prove2.me/submissions/961ced42-d1b9-4413-9809-305c6fe20138

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_natToInt_apply_of_nonneg

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
    (F : (Fin n → ℕ) → ℝ) (k : Fin n → ℕ) :
    aux_natToInt F (natToIntEmbedding k) = F k := by
  have hnonneg : ∀ i, 0 ≤ natToIntEmbedding k i := by
    intro i
    change 0 ≤ (k i : ℤ)
    omega
  rw [natToInt_apply_of_nonneg F (natToIntEmbedding k) hnonneg]
  apply congrArg F
  funext i
  change ((k i : ℤ).toNat) = k i
  apply Int.ofNat.inj
  exact Int.toNat_of_nonneg (by omega)
end Auto.aux_CuboidNorm
