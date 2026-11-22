-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Semantics
-- name    : LeanPool_MatchingLogic_Semantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:20.215304+00:00
-- url     : https://prove2.me/theorems/7cf140b9-7133-4bca-b444-1758e23fad94
-- title:
--   Semantics
-- statement:
--   Definitions and structural lemmas for Semantics, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
def FV : Pattern S Var → Set Var
  | .var x => {x}
  | .bot => ∅
  | .app _ f => ⋃ i, FV (f i)
  | .imp φ ψ => FV φ ∪ FV ψ
  | .ex x φ => FV φ \ {x}
def Closed (φ : Pattern S Var) : Prop := FV φ = ∅
def Model.Total (M : Model S) (ρ : Var → M.carrier) (φ : Pattern S Var) : Prop :=
  M.denote ρ φ = Set.univ
def Model.Sat (M : Model S) (φ : Pattern S Var) : Prop := ∀ ρ, M.Total ρ φ
def Model.SatSet (M : Model S) (Γ : Set (Pattern S Var)) : Prop := ∀ γ ∈ Γ, M.Sat γ
def Model.denoteSet (M : Model S) (ρ : Var → M.carrier)
    (Δ : Set (Pattern S Var)) : Set M.carrier :=
  ⋂ δ ∈ Δ, M.denote ρ δ
def LocalCons (Δ : Set (Pattern S Var)) (φ : Pattern S Var) : Prop :=
  ∀ (M : Model S) (ρ : Var → M.carrier), M.denoteSet ρ Δ ⊆ M.denote ρ φ
def GlobalCons (Γ : Set (Pattern S Var)) (φ : Pattern S Var) : Prop :=
  ∀ M : Model S, M.SatSet Γ → M.Sat φ
end MatchingLogic


