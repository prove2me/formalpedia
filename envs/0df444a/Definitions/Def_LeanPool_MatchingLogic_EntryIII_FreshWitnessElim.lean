-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
-- name    : LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:24:30.308441+00:00
-- url     : https://prove2.me/theorems/ff7dfe6f-b57c-4e1c-b7f9-30ed3f7abed1
-- title:
--   Fresh Witness Elim
-- statement:
--   Definitions and structural lemmas for Fresh Witness Elim, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature}
namespace Pattern
end Pattern
namespace Pattern
def substList : List Nat → List Nat → Pattern S Nat → Pattern S Nat
  | y :: ys, z :: zs, p => substList ys zs (substVar y z p)
  | _, _, p => p
def FreshExListTrace : List Nat → List Nat → Pattern S Nat → Prop
  | [], [], _ => True
  | y :: ys, z :: zs, p =>
      z ∉ (exList ys p).allVars ∧ FreshExListTrace ys zs (substVar y z p)
  | _, _, _ => False
end Pattern
end MatchingLogic


