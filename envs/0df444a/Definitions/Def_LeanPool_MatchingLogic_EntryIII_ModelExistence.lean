-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_ModelExistence
-- name    : LeanPool_MatchingLogic_EntryIII_ModelExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:33:40.916428+00:00
-- url     : https://prove2.me/theorems/baabff3a-988a-4b4d-8a9c-cc27518fb7f7
-- title:
--   Model Existence
-- statement:
--   Definitions and structural lemmas for Model Existence, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/ModelExistence.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Truth
public import Mathlib.Tactic.Bound.Init
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
local instance instDecidableEqPatternNatModelExistence : DecidableEq (Pattern S Nat) :=
  Classical.decEq _
end
end MatchingLogic


