-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Applicative
-- name    : LeanPool_MatchingLogic_Applicative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:16:43.460706+00:00
-- url     : https://prove2.me/theorems/678b3182-b271-49a6-9d99-bfcde940ddb2
-- title:
--   Applicative
-- statement:
--   Definitions and structural lemmas for Applicative, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
namespace Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]
abbrev appSig (Const : Type) : Signature :=
  ⟨Option Const, fun s => match s with | none => 2 | some _ => 0⟩
abbrev appSym : (appSig Const).Sym := none
abbrev coord₁ : Coord (appSig Const) := ⟨none, 0⟩
abbrev coord₂ : Coord (appSig Const) := ⟨none, 1⟩
abbrev ap (φ ψ : Pattern (appSig Const) Var) : Pattern (appSig Const) Var :=
  .app appSym ![φ, ψ]
end Applicative
end MatchingLogic


