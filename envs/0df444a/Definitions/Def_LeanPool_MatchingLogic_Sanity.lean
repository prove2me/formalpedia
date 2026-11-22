-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Sanity
-- name    : LeanPool_MatchingLogic_Sanity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:20.882797+00:00
-- url     : https://prove2.me/theorems/eb41e019-e589-4840-b1be-42489c76584e
-- title:
--   Sanity
-- statement:
--   Definitions and structural lemmas for Sanity, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sanity.lean

module
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
namespace Model
variable {S : Signature}
example :
    let S : Signature := ⟨Unit, fun _ => 1⟩
    let M : Model S := ⟨Bool, ⟨true⟩, fun _ _ => Set.univ⟩
    ¬ M.BackwardClosed {true} := by
  intro S M h
  have : (false : Bool) ∈ ({true} : Set Bool) :=
    h (by rfl) ⟨(), fun _ => false, ⟨0, Nat.zero_lt_one⟩, trivial, rfl⟩
  exact Bool.noConfusion (Set.mem_singleton_iff.mp this)
end Model
end MatchingLogic


