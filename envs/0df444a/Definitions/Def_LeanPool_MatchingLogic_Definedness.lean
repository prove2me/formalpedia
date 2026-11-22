-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Definedness
-- name    : LeanPool_MatchingLogic_Definedness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:18:38.967474+00:00
-- url     : https://prove2.me/theorems/c63e1afe-95a1-46d2-9c94-66087b40cb7d
-- title:
--   Definedness
-- statement:
--   Definitions and structural lemmas for Definedness, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Data.Set.Insert
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
abbrev defSig (S : Signature) : Signature :=
  ⟨Option S.Sym, fun s => match s with | none => 1 | some σ => S.arity σ⟩
def emb : Pattern S Var → Pattern (defSig S) Var
  | .var x => .var x
  | .bot => .bot
  | .imp a b => .imp (emb a) (emb b)
  | .ex x a => .ex x (emb a)
  | .app σ f => .app (some σ) (fun i => emb (f i))
def defined (φ : Pattern (defSig S) Var) : Pattern (defSig S) Var :=
  .app none (fun _ => φ)
def definednessAxiom (x : Var) : Pattern (defSig S) Var := defined (.var x)
def expand (M : Model S) : Model (defSig S) where
  carrier := M.carrier
  nonempty := M.nonempty
  interp := fun s => match s with
    | none => fun _ => Set.univ
    | some σ => fun a => M.interp σ a
end MatchingLogic


