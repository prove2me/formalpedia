-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Composite
-- name    : LeanPool_MatchingLogic_Composite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:49.47159+00:00
-- url     : https://prove2.me/theorems/cf6df3cc-1efd-49c7-ac58-386e07139a30
-- title:
--   Composite
-- statement:
--   Definitions and structural lemmas for Composite, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Locality
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
section Cover
variable (M : Model S) (C : Set M.carrier)
end Cover
end MatchingLogic


