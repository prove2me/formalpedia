-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Boxes
-- name    : LeanPool_MatchingLogic_Boxes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:47.139665+00:00
-- url     : https://prove2.me/theorems/215597c9-914c-4456-9d5b-0692034f1b1d
-- title:
--   Boxes
-- statement:
--   Definitions and structural lemmas for Boxes, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type}
abbrev Coord (S : Signature) : Type := (σ : S.Sym) × Fin (S.arity σ)
def dia (e : Coord S) (ψ : Pattern S Var) : Pattern S Var :=
  .app e.1 (fun j => if j = e.2 then ψ else Pattern.tp)
def box (e : Coord S) (ψ : Pattern S Var) : Pattern S Var :=
  .imp (dia e (.imp ψ .bot)) .bot
def boxes : List (Coord S) → Pattern S Var → Pattern S Var
  | [], ψ => ψ
  | e :: p, ψ => box e (boxes p ψ)
namespace Model
def stepAt (M : Model S) (e : Coord S) (u v : M.carrier) : Prop :=
  ∃ a : Fin (S.arity e.1) → M.carrier, u ∈ M.interp e.1 a ∧ v = a e.2
def reachWord (M : Model S) : List (Coord S) → M.carrier → M.carrier → Prop
  | [], u, v => u = v
  | e :: p, u, v => ∃ w, M.stepAt e u w ∧ M.reachWord p w v
variable (M : Model S)
end Model
section Denotation
variable [DecidableEq Var]
end Denotation
end MatchingLogic


