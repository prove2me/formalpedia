-- Prove2me | Definitions.Def_KirkmanLib_SteinerOp
-- name    : KirkmanLib_SteinerOp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:39:40.136442+00:00
-- url     : https://prove2.me/theorems/1f63a716-1986-43f1-81f4-253ece0c9994
-- title:
--   Steiner Op
-- statement:
--   Definitions and structural lemmas for Steiner Op, from Juan Pablo Traverso Gianini (jtraverso/kirkman-steiner-triple-systems; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kirkman theorem on existence of Steiner triple systems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace Kirkman
variable {P : Type*}
def IsSTSOn [DecidableEq P] (𝒯 : Finset (Finset P)) : Prop :=
  (∀ T ∈ 𝒯, #T = 3) ∧ ∀ x y : P, x ≠ y → ∃! T, T ∈ 𝒯 ∧ x ∈ T ∧ y ∈ T
structure SteinerOp (P : Type*) where
  /-- The operation. -/
  op : P → P → P
  comm : ∀ x y, op x y = op y x
  idem : ∀ x, op x x = x
  cancel : ∀ x y, op x (op x y) = y
namespace SteinerOp
variable (S : SteinerOp P)
variable [DecidableEq P]
def tri (x y : P) : Finset P := {x, y, S.op x y}
variable [Fintype P]
def triples : Finset (Finset P) :=
  (univ.filter (fun p : P × P => p.1 ≠ p.2)).image (fun p => S.tri p.1 p.2)
end SteinerOp
end Kirkman


