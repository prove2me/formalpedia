-- Prove2me | Definitions.Def_BalanceSpecificaton_Entropy
-- name    : BalanceSpecificaton_Entropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:13.23915+00:00
-- url     : https://prove2.me/theorems/a1ca2066-f426-41ab-b554-5587b28dc8b8
-- title:
--   Entropy
-- statement:
--   Definitions and structural lemmas for Entropy, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]
def entropy (X : ShiftSpace A) (_hX : X.carrier.Nonempty) : ℝ :=
  Growth.rate (fun n => (wordCount (language X) n : ℝ))
end BalanceSpecification


