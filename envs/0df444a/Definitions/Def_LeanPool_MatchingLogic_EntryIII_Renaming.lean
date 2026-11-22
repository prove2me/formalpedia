-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
-- name    : LeanPool_MatchingLogic_EntryIII_Renaming
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:35.441809+00:00
-- url     : https://prove2.me/theorems/b0628adf-04e1-4461-b2fe-02433c2aa3e3
-- title:
--   Renaming
-- statement:
--   Definitions and structural lemmas for Renaming, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace Pattern
def rename (f : Var → Var') : Pattern S Var → Pattern S Var'
  | .var x => .var (f x)
  | .app σ args => .app σ (fun i => (args i).rename f)
  | .imp φ ψ => .imp (φ.rename f) (ψ.rename f)
  | .bot => .bot
  | .ex x φ => .ex (f x) (φ.rename f)
end Pattern
def AppCtx.rename (f : Var → Var') : AppCtx S Var → AppCtx S Var'
  | .hole => .hole
  | .node σ i args C => .node σ i (fun j => (args j).rename f) (C.rename f)
end MatchingLogic


