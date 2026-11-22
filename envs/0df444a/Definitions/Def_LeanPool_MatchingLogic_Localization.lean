-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Localization
-- name    : LeanPool_MatchingLogic_Localization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:15.352177+00:00
-- url     : https://prove2.me/theorems/e3b70bf7-0093-4a6d-897d-593fa53ccd3a
-- title:
--   Localization
-- statement:
--   Definitions and structural lemmas for Localization, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
def localize (Γ : Set (Pattern S Var)) : Set (Pattern S Var) :=
  {ψ | ∃ γ ∈ Γ, ∃ p : List (Coord S), ψ = boxes p γ}
end MatchingLogic


