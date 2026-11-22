-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Locality
-- name    : LeanPool_MatchingLogic_Locality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:24.658505+00:00
-- url     : https://prove2.me/theorems/6943926f-92e2-4254-acd9-f875dcf62e07
-- title:
--   Locality
-- statement:
--   Definitions and structural lemmas for Locality, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Locality.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
def AgreeOn {M : Model S} (C : Set M.carrier) (ρ ρ' : Var → M.carrier) : Prop :=
  ∀ x, (ρ x = ρ' x ∧ ρ x ∈ C) ∨ (ρ x ∉ C ∧ ρ' x ∉ C)
end MatchingLogic


