-- Prove2me | Definitions.Def_Focil_Types
-- name    : Focil_Types
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:37:13.804729+00:00
-- url     : https://prove2.me/theorems/d5d5b365-4039-49f8-ab08-530f2bb0f859
-- title:
--   Types
-- statement:
--   Definitions and structural lemmas for Types, from Rahul Barman's pinned FOCIL censorship resistance in the nonce model development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Types.lean

set_option autoImplicit false
namespace Focil
abbrev ValidatorIndex : Type := Nat
structure Transaction where
  /-- A unique identifier; stands in for the RLP hash. -/
  id     : Nat
  /-- The EOA address that signed this transaction. -/
  sender : Nat
  /-- The transaction's nonce relative to its sender. -/
  nonce  : Nat
  /-- The transaction's gas limit. -/
  gas    : Nat
  deriving DecidableEq, Repr
structure InclusionList where
  /-- The slot whose IL committee this list contributes to. -/
  slot            : Nat
  /-- The committee member who authored this list. -/
  validator_index : ValidatorIndex
  /-- The transactions the author wants force-included. -/
  transactions    : List Transaction
  deriving DecidableEq, Repr
structure Block where
  /-- The slot this block was proposed for. -/
  slot         : Nat
  /-- The validator who proposed this block. -/
  proposer     : ValidatorIndex
  /-- The ordered transactions included in the execution payload. -/
  transactions : List Transaction
  /-- The block's gas-limit ceiling. -/
  gasLimit     : Nat
  deriving DecidableEq, Repr
structure FocilState where
  /-- The slot to which this state's IL bucket belongs. -/
  current_slot : Nat
  /-- ILs accepted into the store before the view freeze deadline. -/
  stored_ils   : List InclusionList
  /-- Committee members observed to have equivocated. -/
  equivocators : List ValidatorIndex
  deriving Repr
def IsHonestlyAttributed (state : FocilState) (v : ValidatorIndex) : Prop :=
  v ∉ state.equivocators
def IsConsidered (state : FocilState) (il : InclusionList) : Prop :=
  IsHonestlyAttributed state il.validator_index
end Focil


