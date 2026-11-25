-- Prove2me | Definitions.Def_Euler_Petersen
-- name    : Euler_Petersen
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:38:12.100323+00:00
-- url     : https://prove2.me/theorems/25721cbb-2c9b-470e-8632-c337ac38fe22
-- title:
--   Petersen
-- statement:
--   Definitions and structural lemmas for Petersen, from Juan Pablo Traverso Gianini (jtraverso/euler-petersen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Euler's theorem on Eulerian circuits and trails, and Petersen's 2-factor theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Petersen.lean

module
public import Definitions.Def_Euler_Orientation
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Set.Card
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SimpleGraph
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
def permGraph (σ : Equiv.Perm V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ (σ u = w ∨ σ w = u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
variable {G : SimpleGraph V} [DecidableRel G.Adj]
end SimpleGraph


