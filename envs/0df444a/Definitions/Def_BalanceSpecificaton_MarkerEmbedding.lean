-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkerEmbedding
-- name    : BalanceSpecificaton_MarkerEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:32:11.897552+00:00
-- url     : https://prove2.me/theorems/5b570d34-2354-4e33-8b9d-36a42a77a606
-- title:
--   Marker Embedding
-- statement:
--   Definitions and structural lemmas for Marker Embedding, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.MarkerEmbedding
variable {A B : Type*}
def mapConfiguration (f : A → B) (x : Configuration A) : Configuration B :=
  fun k => f (x k)
theorem mapConfiguration_shift (f : A → B) (x : Configuration A) (k : ℤ) :
    mapConfiguration f (SymbolicDynamics.FullShift.shift k x) =
      SymbolicDynamics.FullShift.shift k (mapConfiguration f x) := rfl
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace B] [T2Space B]
omit [Fintype A] [T2Space B] in
theorem continuous_mapConfiguration (f : A → B) : Continuous (mapConfiguration f) := by
  apply continuous_pi
  intro k
  exact (continuous_of_discreteTopology : Continuous f).comp (continuous_apply k)
def renamedShift (f : A → B) (Y : ShiftSpace A) : ShiftSpace B where
  carrier := mapConfiguration f '' Y.carrier
  isClosed := (Y.isClosed.isCompact.image (continuous_mapConfiguration f)).isClosed
  mapsTo := by
    rintro k y ⟨x, hx, rfl⟩
    exact ⟨SymbolicDynamics.FullShift.shift k x, Y.mapsTo k hx, mapConfiguration_shift f x k⟩
theorem renamedShift_nonempty (f : A → B) {Y : ShiftSpace A}
    (hY : Y.carrier.Nonempty) : (renamedShift f Y).carrier.Nonempty := by
  obtain ⟨x, hx⟩ := hY
  exact ⟨mapConfiguration f x, x, hx, rfl⟩
end BalanceSpecification.MarkerEmbedding


