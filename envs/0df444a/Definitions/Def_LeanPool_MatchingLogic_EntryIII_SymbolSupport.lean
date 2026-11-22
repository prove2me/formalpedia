-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
-- name    : LeanPool_MatchingLogic_EntryIII_SymbolSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:33.115454+00:00
-- url     : https://prove2.me/theorems/0a7150da-f05d-42f0-81c7-33c51effad8a
-- title:
--   Symbol Support
-- statement:
--   Definitions and structural lemmas for Symbol Support, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SymbolSupport.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type}
namespace Pattern
def symbolSupport [DecidableEq S.Sym] : Pattern S Var → Finset S.Sym
  | .var _ => ∅
  | .bot => ∅
  | .app sigma args => insert sigma (Finset.univ.biUnion (fun i => (args i).symbolSupport))
  | .imp phi psi => phi.symbolSupport ∪ psi.symbolSupport
  | .ex _ phi => phi.symbolSupport
end Pattern
end MatchingLogic


