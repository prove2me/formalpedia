-- Prove2me | Definitions.Def_Focil_AccountState
-- name    : Focil_AccountState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:37:30.240635+00:00
-- url     : https://prove2.me/theorems/4bb39db9-e17f-42d8-8365-732d24e70356
-- title:
--   Account State
-- statement:
--   Definitions and structural lemmas for Account State, from Rahul Barman's pinned FOCIL censorship resistance in the nonce model development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/AccountState.lean

import Definitions.Def_Focil_Types
set_option autoImplicit false
namespace Focil
abbrev Sender : Type := Nat
abbrev AccountState : Type := Sender → Nat
def AccountState.initial : AccountState := fun _ => 0
def applyTx (state : AccountState) (tx : Transaction) : AccountState :=
  fun s =>
    if s = tx.sender ∧ tx.nonce = state tx.sender then
      state s + 1
    else
      state s
def postState (initial : AccountState) (txs : List Transaction) : AccountState :=
  txs.foldl applyTx initial
def canAppendNonce (state : AccountState) (tx : Transaction) : Prop :=
  tx.nonce = state tx.sender
def canAppendToBlock (initial : AccountState) (b : Block)
    (tx : Transaction) : Prop :=
  canAppendNonce (postState initial b.transactions) tx
end Focil


