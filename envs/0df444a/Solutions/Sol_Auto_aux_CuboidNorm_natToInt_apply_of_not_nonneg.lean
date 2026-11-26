-- Prove2me | solution 1 for Auto.aux_CuboidNorm.natToInt_apply_of_not_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:56.088238+00:00
-- url     : https://prove2.me/submissions/24ddf51c-a45e-4ee9-9a05-031f1f0415f8

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
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
theorem _root_.solution {n : ℕ}
    (F : (Fin n → ℕ) → ℝ) (k : ZVector n) (hk : ¬ ∀ i, 0 ≤ k i) :
    aux_natToInt F k = 0 := by
  simp [aux_natToInt, hk]
end Auto.aux_CuboidNorm
