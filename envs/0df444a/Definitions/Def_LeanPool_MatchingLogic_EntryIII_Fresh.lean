-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
-- name    : LeanPool_MatchingLogic_EntryIII_Fresh
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:47.023251+00:00
-- url     : https://prove2.me/theorems/efa45e9a-9e59-4b5c-815d-356e315ccefe
-- title:
--   Fresh
-- statement:
--   Definitions and structural lemmas for Fresh, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Fresh.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace Pattern
def allVars : Pattern S Var → Finset Var
  | .var x => {x}
  | .bot => ∅
  | .app _ args => Finset.univ.biUnion (fun i => (args i).allVars)
  | .imp phi psi => phi.allVars ∪ psi.allVars
  | .ex x phi => insert x phi.allVars
def fresh (p : Pattern S Nat) : Nat :=
  (insert 0 p.allVars).max' (Finset.insert_nonempty 0 p.allVars) + 1
end Pattern
end MatchingLogic


