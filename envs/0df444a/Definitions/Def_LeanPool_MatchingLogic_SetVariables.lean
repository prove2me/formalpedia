-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_SetVariables
-- name    : LeanPool_MatchingLogic_SetVariables
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:51.07165+00:00
-- url     : https://prove2.me/theorems/8483c72f-81fd-431d-82ca-8d641e119fb4
-- title:
--   Set Variables
-- statement:
--   Definitions and structural lemmas for Set Variables, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Set.Insert
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
namespace SetVariables
variable {S : Signature} {Var SVar : Type} [DecidableEq Var]
inductive SPattern (S : Signature) (Var SVar : Type) where
  | var : Var → SPattern S Var SVar
  | svar : SVar → SPattern S Var SVar
  | app : (σ : S.Sym) → (Fin (S.arity σ) → SPattern S Var SVar) → SPattern S Var SVar
  | imp : SPattern S Var SVar → SPattern S Var SVar → SPattern S Var SVar
  | bot : SPattern S Var SVar
  | ex : Var → SPattern S Var SVar → SPattern S Var SVar
structure SVal (M : Model S) (Var SVar : Type) where
  /-- The valuation of element variables. -/
  elem : Var → M.carrier
  /-- The valuation of set variables. -/
  sets : SVar → Set M.carrier
def sdenote (M : Model S) : SVal M Var SVar → SPattern S Var SVar → Set M.carrier
  | ρ, .var x => {ρ.elem x}
  | ρ, .svar X => ρ.sets X
  | _, .bot => ∅
  | ρ, .app σ f => M.app σ (fun i => sdenote M ρ (f i))
  | ρ, .imp a b => (sdenote M ρ a)ᶜ ∪ sdenote M ρ b
  | ρ, .ex x a => ⋃ v : M.carrier, sdenote M ⟨Function.update ρ.elem x v, ρ.sets⟩ a
def SSat (M : Model S) (φ : SPattern S Var SVar) : Prop :=
  ∀ ρ : SVal M Var SVar, sdenote M ρ φ = Set.univ
def SGlobalCons (Γ : Set (SPattern S Var SVar)) (φ : SPattern S Var SVar) : Prop :=
  ∀ M : Model S, (∀ γ ∈ Γ, SSat M γ) → SSat M φ
abbrev constSig : Signature := ⟨Unit, fun _ => 0⟩
abbrev dPat : Pattern constSig Var := .app () (fun i => i.elim0)
abbrev fullConstModel : Model constSig :=
  ⟨Unit, ⟨()⟩, fun _ _ => Set.univ⟩
end SetVariables
end MatchingLogic


