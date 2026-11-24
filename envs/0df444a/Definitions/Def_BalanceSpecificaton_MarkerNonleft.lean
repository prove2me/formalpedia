-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkerNonleft
-- name    : BalanceSpecificaton_MarkerNonleft
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:31.74596+00:00
-- url     : https://prove2.me/theorems/a2978c0f-ea8e-4268-ad15-86284d8d704b
-- title:
--   Marker Nonleft
-- statement:
--   Definitions and structural lemmas for Marker Nonleft, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] [TopologicalSpace (Option A)]
def markerPairFinset (X : ShiftSpace (Option A)) (Y : ShiftSpace A) (n : ℕ) :
    Finset ((_k : Fin n) × (Word (Option A) × Word A)) :=
  Finset.univ.sigma fun k =>
    (predecessorFinset (language X) [none] (k.val + 1)).product
      (wordFinset (language Y) (n - 1 - k.val))
end BalanceSpecification


