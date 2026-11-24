-- Prove2me | Definitions.Def_BalanceSpecificaton_ProductShift
-- name    : BalanceSpecificaton_ProductShift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:37:48.484888+00:00
-- url     : https://prove2.me/theorems/16ce0670-3021-45ef-bf3e-916258f19d7b
-- title:
--   Product Shift
-- statement:
--   Definitions and structural lemmas for Product Shift, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}
def productShift [TopologicalSpace A] [TopologicalSpace B]
    (X : ShiftSpace A) (Y : ShiftSpace B) : ShiftSpace (A × B) where
  carrier := {z | (fun i => (z i).1) ∈ X.carrier ∧ (fun i => (z i).2) ∈ Y.carrier}
  isClosed :=
    (X.isClosed.preimage (by fun_prop)).inter (Y.isClosed.preimage (by fun_prop))
  mapsTo := by
    intro k z hz
    exact ⟨X.mapsTo k hz.1, Y.mapsTo k hz.2⟩
theorem productShift_nonempty [TopologicalSpace A] [TopologicalSpace B]
    {X : ShiftSpace A} {Y : ShiftSpace B}
    (hX : X.carrier.Nonempty) (hY : Y.carrier.Nonempty) :
    (productShift X Y).carrier.Nonempty := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  exact ⟨fun i => (x i, y i), hx, hy⟩
def unrestrictedShift (A : Type*) [TopologicalSpace A] : ShiftSpace A :=
  SymbolicDynamics.FullShift.fullShift A ℤ
theorem unrestrictedShift_nonempty [TopologicalSpace A] [Nonempty A] :
    (unrestrictedShift A).carrier.Nonempty := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨fun _ => a, Set.mem_univ _⟩
def constantShift [TopologicalSpace A] [T1Space A] (a : A) : ShiftSpace A where
  carrier := {fun _ => a}
  isClosed := isClosed_singleton
  mapsTo := by
    intro k x hx
    rw [Set.mem_singleton_iff] at hx ⊢
    subst x
    rfl
theorem constantShift_nonempty [TopologicalSpace A] [T1Space A] (a : A) :
    (constantShift a).carrier.Nonempty := ⟨fun _ => a, Set.mem_singleton _⟩
end BalanceSpecification


