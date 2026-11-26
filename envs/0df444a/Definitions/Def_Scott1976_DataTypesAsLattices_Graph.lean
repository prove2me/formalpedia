-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Graph
-- name    : Scott1976_DataTypesAsLattices_Graph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:53:07.545565+00:00
-- url     : https://prove2.me/theorems/bfae44f4-fea8-4a82-a3ba-f5aff493f395
-- title:
--   Graph
-- statement:
--   Definitions and structural lemmas for Graph, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}
def funOf (u : Pomega) (x : Pomega) : Pomega :=
  {m | ∃ n, e n ⊆ x ∧ pair n m ∈ u}
infixl:70 " ⬝ " => funOf
def IsGraph (u : Pomega) : Prop :=
  ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u
def lam (τ : Pomega → Pomega) : Pomega := graph τ
end Scott1976.DataTypesAsLattices


