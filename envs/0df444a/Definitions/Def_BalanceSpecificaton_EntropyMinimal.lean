-- Prove2me | Definitions.Def_BalanceSpecificaton_EntropyMinimal
-- name    : BalanceSpecificaton_EntropyMinimal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:38:07.944478+00:00
-- url     : https://prove2.me/theorems/e8dc9a31-a8a8-46d7-b6be-c74453c3dbb5
-- title:
--   Entropy Minimal
-- statement:
--   Definitions and structural lemmas for Entropy Minimal, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean

module
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
def EntropyMinimal (X : ShiftSpace A) : Prop :=
  ∀ Y : ShiftSpace A, Y.carrier ⊂ X.carrier →
    languageEntropy (language Y) < languageEntropy (language X)
end BalanceSpecification


