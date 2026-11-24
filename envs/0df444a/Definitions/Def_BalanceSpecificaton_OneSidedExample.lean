-- Prove2me | Definitions.Def_BalanceSpecificaton_OneSidedExample
-- name    : BalanceSpecificaton_OneSidedExample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:36:15.999997+00:00
-- url     : https://prove2.me/theorems/c4b63273-ce09-4cf6-814c-41715c8f0765
-- title:
--   One Sided Example
-- statement:
--   Definitions and structural lemmas for One Sided Example, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedExample.lean

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification.OneSidedExample
abbrev Alphabet := Fin 3
instance : TopologicalSpace Alphabet := ⊥
instance : DiscreteTopology Alphabet := ⟨rfl⟩
abbrev a : Alphabet := 0
abbrev b : Alphabet := 1
abbrev c : Alphabet := 2
def code : Set (Word Alphabet) :=
  {w | w = [c] ∨
    (∃ n : ℕ, 1 ≤ n ∧ w = List.replicate n a ++ List.replicate n b) ∨
    ∃ l m : ℕ, 1 ≤ m ∧ m < l ∧
      w = List.replicate l a ++ List.replicate m b ++ [c]}
def shift : ShiftSpace Alphabet := codedShift code
end BalanceSpecification.OneSidedExample


