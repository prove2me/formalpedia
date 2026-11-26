-- Prove2me | solution 1 for Auto.aux_orbit_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:00.07851+00:00
-- url     : https://prove2.me/submissions/c8d7bc8b-586f-417c-bfcb-f2dab31493cf

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
    (S : Fin n → X → X) (k : Fin n → ℕ) (h : X → X)
    (_hcomm : ∀ i, Function.Commute h (S i)),
      Function.Commute h (aux_orbit S k)
  | 0, S, k, h, _hcomm => by
      intro x
      rfl
  | n + 1, S, k, h, hcomm => by
      rw [aux_orbit_succ]
      apply Function.Commute.comp_right
      · exact (hcomm 0).iterate_right (k 0)
      · apply solution
        intro i
        exact hcomm i.succ
end Auto
