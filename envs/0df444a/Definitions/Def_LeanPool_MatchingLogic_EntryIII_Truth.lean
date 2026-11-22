-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_Truth
-- name    : LeanPool_MatchingLogic_EntryIII_Truth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:32:57.861794+00:00
-- url     : https://prove2.me/theorems/87ae63be-df65-4da4-8aa7-8e19a1617704
-- title:
--   Truth
-- statement:
--   Definitions and structural lemmas for Truth, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Truth.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
open scoped BigOperators
variable {S : Signature}
noncomputable section
local instance instDecidableEqPatternNatTruth : DecidableEq (Pattern S Nat) :=
  Classical.decEq _
end
end MatchingLogic


