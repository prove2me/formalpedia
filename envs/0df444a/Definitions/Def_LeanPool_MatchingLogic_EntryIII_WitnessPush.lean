-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
-- name    : LeanPool_MatchingLogic_EntryIII_WitnessPush
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:24:07.688504+00:00
-- url     : https://prove2.me/theorems/f04f2255-2dfd-4d85-8f4a-36d67a91e7b9
-- title:
--   Witness Push
-- statement:
--   Definitions and structural lemmas for Witness Push, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature}
namespace Pattern
def exList : List Nat -> Pattern S Nat -> Pattern S Nat
  | [], p => p
  | y :: ys, p => .ex y (exList ys p)
end Pattern
namespace Pattern
def exOn {n : Nat} (is : List (Fin n)) (y : Fin n -> Nat)
    (body : Fin n -> Pattern S Nat) : Fin n -> Pattern S Nat :=
  fun i => if i ∈ is then .ex (y i) (body i) else body i
end Pattern
end MatchingLogic


