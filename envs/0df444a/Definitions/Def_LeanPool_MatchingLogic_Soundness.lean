-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Soundness
-- name    : LeanPool_MatchingLogic_Soundness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:26.456732+00:00
-- url     : https://prove2.me/theorems/b23f2841-59b9-4c42-a624-de77e0bc8ac8
-- title:
--   Soundness
-- statement:
--   Definitions and structural lemmas for Soundness, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Soundness.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
public import Mathlib.Data.Set.BooleanAlgebra
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
attribute [local instance] Classical.propDecidable
end MatchingLogic


