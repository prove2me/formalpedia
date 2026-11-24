-- Prove2me | Definitions.Def_BalanceSpecificaton_LanguageProperties
-- name    : BalanceSpecificaton_LanguageProperties
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:30:15.740147+00:00
-- url     : https://prove2.me/theorems/2c7491fe-0364-483d-bae8-f73fe2f53e14
-- title:
--   Language Properties
-- statement:
--   Definitions and structural lemmas for Language Properties, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
end BalanceSpecification


