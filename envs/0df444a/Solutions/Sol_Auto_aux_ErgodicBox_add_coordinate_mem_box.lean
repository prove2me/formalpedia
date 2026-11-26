-- Prove2me | solution 1 for Auto.aux_ErgodicBox.add_coordinate_mem_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:28.743456+00:00
-- url     : https://prove2.me/submissions/a845cbae-0653-4e59-b944-76d7b01777b9

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_mem_box
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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution {n L M : ℕ} (k : Fin n → ℕ)
    (hk : k ∈ box n L) (i : Fin n) (m : ℕ) (hm : m < M) :
    k + aux_coordinate i m ∈ box n (L + M) := by
  rw [mem_box]
  intro j
  by_cases hji : j = i
  · subst j
    have hki : k i < L := (mem_box k).mp hk i
    simp [Pi.add_apply, aux_coordinate]
    omega
  · simp [Pi.add_apply, aux_coordinate, hji]
    have hkj : k j < L := (mem_box k).mp hk j
    omega
end Auto.aux_ErgodicBox
