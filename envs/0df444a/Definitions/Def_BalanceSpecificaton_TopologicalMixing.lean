-- Prove2me | Definitions.Def_BalanceSpecificaton_TopologicalMixing
-- name    : BalanceSpecificaton_TopologicalMixing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:51:08.035451+00:00
-- url     : https://prove2.me/theorems/b7d7b2a4-0279-48ba-8b19-1dd894f81087
-- title:
--   Topological Mixing
-- statement:
--   Definitions and structural lemmas for Topological Mixing, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TopologicalMixing.lean

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set TopologicalSpace
namespace BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
def TopologicallyMixing (X : ShiftSpace A) : Prop :=
  ∀ U V : Set X.carrier, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    ∀ᶠ n : ℕ in Filter.atTop, (U ∩ (shiftMap X)^[n] ⁻¹' V).Nonempty
namespace FiveSymbol
end FiveSymbol
end BalanceSpecification


