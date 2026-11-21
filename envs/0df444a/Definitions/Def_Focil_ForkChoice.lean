-- Prove2me | Definitions.Def_Focil_ForkChoice
-- name    : Focil_ForkChoice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:37:43.175616+00:00
-- url     : https://prove2.me/theorems/1600f056-c65c-42f8-baad-2735aacc0515
-- title:
--   Fork Choice
-- statement:
--   Definitions and structural lemmas for Fork Choice, from Rahul Barman's pinned FOCIL censorship resistance in the nonce model development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/ForkChoice.lean

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
set_option autoImplicit false
namespace Focil
structure ForkChoice where
  /-- The fork-choice store snapshot at attestation time. -/
  state       : FocilState
  /--
    Validity predicate (formal counterpart of "EVM-valid
    appendability"). Bundled here so concrete instances can
    pin a specific model (e.g. nonce/balance proxy from
    `Focil/AccountState.lean`) and the safety chain reads the
    same predicate everywhere.
  -/
  canAppend   : Transaction → Block → Prop
  /-- The block-fullness model in force for this run. -/
  full        : Block → Prop
  /-- Validators who behave honestly in this run. -/
  IsHonest    : ValidatorIndex → Prop
  /-- Predicate: this block has a quorum of attestations. -/
  HasQuorum   : Block → Prop
  /-- Per-validator/block vote relation. -/
  Voted       : ValidatorIndex → Block → Prop
  /--
    Soundness obligation: a block with a quorum has at least one
    validator who is honest *and* voted for it.
  -/
  quorum_has_honest_voter :
    ∀ b : Block, HasQuorum b →
      ∃ v : ValidatorIndex, IsHonest v ∧ Voted v b
  /--
    Soundness obligation: honest validators only vote for blocks
    that are FOCIL-compliant against the bundled `state` under
    the bundled `canAppend` and `full` models.
  -/
  honest_attester_compliance :
    ∀ (b : Block) (v : ValidatorIndex),
      IsHonest v →
      Voted v b →
      FocilCompliant canAppend full b state
def IsCanonical (fc : ForkChoice) (b : Block) : Prop :=
  fc.HasQuorum b
end Focil


