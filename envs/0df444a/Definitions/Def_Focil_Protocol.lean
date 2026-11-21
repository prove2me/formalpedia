-- Prove2me | Definitions.Def_Focil_Protocol
-- name    : Focil_Protocol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:37:28.836278+00:00
-- url     : https://prove2.me/theorems/a1e59f8c-40fc-4e45-8cf6-35dbf602ac31
-- title:
--   Protocol
-- statement:
--   Definitions and structural lemmas for Protocol, from Rahul Barman's pinned FOCIL censorship resistance in the nonce model development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Protocol.lean

import Definitions.Def_Focil_Types
set_option autoImplicit false
namespace Focil
opaque CanAppend : Transaction → Block → Prop
def CompliantWith
    (canAppend : Transaction → Block → Prop)
    (full : Block → Prop)
    (b : Block) (il : InclusionList) : Prop :=
  ∀ tx ∈ il.transactions,
    tx ∈ b.transactions ∨ ¬ canAppend tx b ∨ full b
def FocilCompliant
    (canAppend : Transaction → Block → Prop)
    (full : Block → Prop)
    (b : Block) (state : FocilState) : Prop :=
  ∀ il ∈ state.stored_ils,
    IsConsidered state il → CompliantWith canAppend full b il
end Focil


