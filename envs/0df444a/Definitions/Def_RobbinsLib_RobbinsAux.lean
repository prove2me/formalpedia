-- Prove2me | Definitions.Def_RobbinsLib_RobbinsAux
-- name    : RobbinsLib_RobbinsAux
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:20:37.417751+00:00
-- url     : https://prove2.me/theorems/29de4039-352f-5635-9954-bd6de066e4cf
-- title:
--   Robbins Aux
-- statement:
--   Definitions and structural lemmas for Robbins Aux, from Juan Pablo Traverso Gianini (jtraverso/robbins-strong-orientation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Robbins' theorem on strongly connected orientations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace Robbins
variable {V : Type*} (G : SimpleGraph V)
structure Inv (D : V → V → Prop) : Prop where
  sub : ∀ a b, D a b → G.Adj a b
  anti : ∀ a b, D a b → ¬ D b a
  ret : ∀ a b, D a b → Relation.ReflTransGen D b a
variable {G}
end Robbins


