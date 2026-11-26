-- Prove2me | solution 1 for Auto.aux_orbit_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:12.617571+00:00
-- url     : https://prove2.me/submissions/40aca46c-a4f2-4878-a16f-457b565353e2

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_orbit_commute
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
theorem _root_.solution {X : Type*} : ∀ {n : ℕ} (S : Fin n → X → X)
    (_ : ∀ i j, Function.Commute (S i) (S j)) (k l : Fin n → ℕ),
    aux_orbit S (k + l) = aux_orbit S k ∘ aux_orbit S l
  | 0, S, _hS, k, l => rfl
  | n + 1, S, hS, k, l => by
      rw [aux_orbit_succ, aux_orbit_succ, aux_orbit_succ]
      simp only [Pi.add_apply]
      rw [Function.iterate_add]
      have htail : ∀ (i j : Fin n), Function.Commute (S i.succ) (S j.succ) := by
        intro i j
        exact hS i.succ j.succ
      change ((S 0)^[k 0] ∘ (S 0)^[l 0]) ∘
          aux_orbit (fun i ↦ S i.succ) ((fun i ↦ k i.succ) + fun i ↦ l i.succ) =
        ((S 0)^[k 0] ∘ aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ)) ∘
          (S 0)^[l 0] ∘ aux_orbit (fun i ↦ S i.succ) (fun i ↦ l i.succ)
      rw [solution (fun i ↦ S i.succ) htail (fun i ↦ k i.succ)
        (fun i ↦ l i.succ)]
      ext x
      simp only [Function.comp_apply]
      rw [aux_orbit_commute (fun i ↦ S i.succ) (fun i ↦ k i.succ)
        ((S 0)^[l 0]) (fun i ↦ (hS 0 i.succ).iterate_left (l 0))]
end Auto
