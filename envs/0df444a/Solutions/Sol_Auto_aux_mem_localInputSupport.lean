-- Prove2me | solution 1 for Auto.aux_mem_localInputSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:49:38.882265+00:00
-- url     : https://prove2.me/submissions/24d63172-43db-44a3-a49c-59c03d68a290

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
namespace Auto
theorem _root_.solution {n : ℕ}
    {B : Finset (Fin n → ℕ)} {L : ℕ} {k : Fin n → ℕ} (hk : k ∈ B)
    (i : Fin n) {m : ℕ} (hm : m < L) :
    k + aux_coordinate i m ∈ aux_localInputSupport B L := by
  classical
  simp only [aux_localInputSupport, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image, Finset.mem_range]
  exact ⟨k, hk, i, m, hm, rfl⟩
end Auto
