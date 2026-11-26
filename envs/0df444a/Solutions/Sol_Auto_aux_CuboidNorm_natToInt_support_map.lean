-- Prove2me | solution 1 for Auto.aux_CuboidNorm.natToInt_support_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:50:03.522105+00:00
-- url     : https://prove2.me/submissions/50fc0b36-5f16-4f7f-8010-7dab1e2fce61

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_natToInt_apply_of_nonneg
public import Theorems.Thm_Auto_aux_CuboidNorm_natToInt_apply_of_not_nonneg
section
@[expose] public section
namespace Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
@[simp] private theorem aux_orbit_zero {X : Type*} (S : Fin 0 → X → X)
    (k : Fin 0 → ℕ) : aux_orbit S k = id :=
  rfl
@[simp] private theorem aux_orbit_succ {X : Type*} {n : ℕ}
    (S : Fin (n + 1) → X → X) (k : Fin (n + 1) → ℕ) :
    aux_orbit S k = (S 0)^[k 0] ∘
      aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ) :=
  rfl
section
universe v
end
namespace aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
end aux_CuboidNorm
namespace aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
end aux_ErgodicBox
end
end Auto
end
end

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
theorem _root_.solution {n : ℕ} (A : Finset (Fin n → ℕ))
    (F : (Fin n → ℕ) → ℝ) (hsupport : ∀ k, k ∉ A → F k = 0) :
    ∀ z, z ∉ A.map natToIntEmbedding → aux_natToInt F z = 0 := by
  intro z hz
  by_cases hnonneg : ∀ i, 0 ≤ z i
  · rw [natToInt_apply_of_nonneg F z hnonneg]
    have hnot : (fun i ↦ (z i).toNat) ∉ A := by
      intro hm
      apply hz
      rw [Finset.mem_map]
      refine ⟨(fun i ↦ (z i).toNat), hm, ?_⟩
      ext i
      change ((z i).toNat : ℤ) = z i
      exact Int.toNat_of_nonneg (hnonneg i)
    exact hsupport _ hnot
  · exact natToInt_apply_of_not_nonneg F z hnonneg
end Auto.aux_CuboidNorm
