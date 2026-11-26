-- Prove2me | solution 1 for Auto.aux_orbit_add_coordinate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:10.350687+00:00
-- url     : https://prove2.me/submissions/f6257b4f-1652-4bc2-8c4e-fd7a88ce8808

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_orbit_add
public import Theorems.Thm_Auto_aux_orbit_coordinate
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
theorem _root_.solution {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (S : ErgodicSystem X μ n) (k : Fin n → ℕ) (i : Fin n)
    (m : ℕ) (x : X) :
    aux_orbit S.transformation (k + aux_coordinate i m) x =
      (S.transformation i)^[m] (aux_orbit S.transformation k x) := by
  have hadd : k + aux_coordinate i m = aux_coordinate i m + k := by
    ext j
    simp only [Pi.add_apply]
    ac_rfl
  rw [hadd, aux_orbit_add S.transformation S.commutes,
    aux_orbit_coordinate]
  rfl
end Auto
