-- Prove2me | solution 1 for Auto.aux_orbit_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:39:28.259922+00:00
-- url     : https://prove2.me/submissions/3740ce65-978e-4e94-aa0c-0d79fec3e8fc

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_orbit_zero_vector
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
theorem _root_.solution {X : Type*} : ∀ {n : ℕ}
    (S : Fin n → X → X) (i : Fin n) (m : ℕ),
    aux_orbit S (aux_coordinate i m) = (S i)^[m]
  | 0, S, i, m => Fin.elim0 i
  | n + 1, S, i, m => by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [aux_orbit_succ]
        change (S 0)^[m] ∘ aux_orbit (fun i ↦ S i.succ) 0 = (S 0)^[m]
        rw [aux_orbit_zero_vector, Function.comp_id]
      · rw [aux_orbit_succ]
        have hzero : aux_coordinate j.succ m 0 = 0 := by
          have hne : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
          simp [aux_coordinate, hne]
        rw [hzero, Function.iterate_zero, Function.id_comp]
        have htail : (fun j' : Fin n ↦ aux_coordinate j.succ m j'.succ) =
            aux_coordinate j m := by
          ext j'
          simp [aux_coordinate]
        rw [htail, solution]
end Auto
