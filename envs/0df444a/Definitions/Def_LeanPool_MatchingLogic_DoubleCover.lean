-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_DoubleCover
-- name    : LeanPool_MatchingLogic_DoubleCover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:54.251927+00:00
-- url     : https://prove2.me/theorems/a161a161-e75b-4b61-98cf-6dbc0e7418a7
-- title:
--   Double Cover
-- statement:
--   Definitions and structural lemmas for Double Cover, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/DoubleCover.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
section Cover
variable (M : Model S) (C : Set M.carrier)
def coverInterp (σ : S.Sym) (A : Fin (S.arity σ) → (C × Bool)) : Set (C × Bool) :=
  {p | (∀ j, (A j).2 = p.2) ∧
       ((p.1 : M.carrier) ∈ M.interp σ (fun j => ((A j).1 : M.carrier)))}
def cover (hne : C.Nonempty) : Model S where
  carrier := C × Bool
  nonempty := ⟨(⟨hne.choose, hne.choose_spec⟩, false)⟩
  interp := coverInterp M C
def proj (star : M.carrier) (i : Bool) (p : C × Bool) : M.carrier :=
  if p.2 = i then (p.1 : M.carrier) else star
end Cover
end MatchingLogic


