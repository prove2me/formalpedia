-- Prove2me | Definitions.Def_BalanceSpecificaton_Occurrence
-- name    : BalanceSpecificaton_Occurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:30:54.359808+00:00
-- url     : https://prove2.me/theorems/c6052c57-28c3-40b0-96af-081b5529c56a
-- title:
--   Occurrence
-- statement:
--   Definitions and structural lemmas for Occurrence, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
def avoidingLanguage (L : Set (Word A)) (v : Word A) : Set (Word A) :=
  {w | w ∈ L ∧ ¬v <:+: w}
omit [Fintype A] in
/-- Avoidance of one word preserves factoriality. -/
theorem IsFactorial.avoidingLanguage (hL : IsFactorial L) (v : Word A) :
    IsFactorial (avoidingLanguage L v) := by
  intro u w huw hw
  exact ⟨hL huw hw.1, fun hvu => hw.2 (hvu.trans huw)⟩
namespace Growth
end Growth
end BalanceSpecification


