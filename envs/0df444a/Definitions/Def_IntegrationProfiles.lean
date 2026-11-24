-- Prove2me | Definitions.Def_IntegrationProfiles
-- name    : IntegrationProfiles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:24:36.205302+00:00
-- url     : https://prove2.me/theorems/f3a3f0a0-0e49-4b31-8635-29a09a8402c3
-- title:
--   Integration Profiles
-- statement:
--   Definitions and structural lemmas for Integration Profiles, from shentonyan (shentonyan/sealed-bid-award-erc; see pinned CC0-1.0 LICENSE.md)'s pinned Truthful bidding dominance for ERC-8469 sealed-bid Vickrey awards development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/IntegrationProfiles.lean

set_option autoImplicit true
namespace IntegrationProfiles
def ranks (r : Nat) (before after : List Nat) (b : Nat) : Prop :=
  b ≤ r ∧ (∀ x ∈ before, b < x) ∧ (∀ x ∈ after, b ≤ x)
instance (r : Nat) (before after : List Nat) (b : Nat) : Decidable (ranks r before after b) := by
  unfold ranks; exact inferInstance
def fixedRewardUtility (reward r : Nat) (before after : List Nat) (c b : Nat) : Int :=
  if ranks r before after b then (reward : Int) - c else 0
def postedWins (r : Nat) (earlierAccepted : Bool) (b : Nat) : Prop :=
  b ≤ r ∧ earlierAccepted = false
instance (r : Nat) (e : Bool) (b : Nat) : Decidable (postedWins r e b) := by
  unfold postedWins; exact inferInstance
def postedUtility (r : Nat) (e : Bool) (c b : Nat) : Int :=
  if postedWins r e b then (r : Int) - c else 0
def accept (r c : Nat) : Nat := if c ≤ r then r else r + 1
end IntegrationProfiles


