-- Prove2me | Definitions.Def_VickreyTruthful
-- name    : VickreyTruthful
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:24:35.503815+00:00
-- url     : https://prove2.me/theorems/cfe45ab2-837b-4d32-a352-c102e03269cc
-- title:
--   Vickrey Truthful
-- statement:
--   Definitions and structural lemmas for Vickrey Truthful, from shentonyan (shentonyan/sealed-bid-award-erc; see pinned CC0-1.0 LICENSE.md)'s pinned Truthful bidding dominance for ERC-8469 sealed-bid Vickrey awards development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean

set_option autoImplicit true
namespace VickreyAward
def price (r : Nat) (before after : List Nat) : Nat :=
  (before ++ after).foldr min r
def wins (r : Nat) (before after : List Nat) (b : Nat) : Prop :=
  b ≤ r ∧ (∀ x ∈ before, b < x) ∧ (∀ x ∈ after, b ≤ x)
instance (r : Nat) (before after : List Nat) (b : Nat) : Decidable (wins r before after b) := by
  unfold wins; exact inferInstance
def utility (r : Nat) (before after : List Nat) (c b : Nat) : Int :=
  if wins r before after b then (price r before after : Int) - c else 0
def firstPriceUtility (r : Nat) (before after : List Nat) (c b : Nat) : Int :=
  if wins r before after b then (b : Int) - c else 0
example : firstPriceUtility 100 [] [80] 40 79 > firstPriceUtility 100 [] [80] 40 40 := by
  decide
end VickreyAward


