-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
-- name    : Scott1976_DataTypesAsLattices_Continuous
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:52:42.711276+00:00
-- url     : https://prove2.me/theorems/d5f722b2-7445-41b9-b431-9de7f00bc906
-- title:
--   Continuous
-- statement:
--   Definitions and structural lemmas for Continuous, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def basicNhhd (n : ℕ) : Set Pomega := {x | e n ⊆ x}
def IsScottOpen (U : Set Pomega) : Prop :=
  ∃ B : Set ℕ, U = ⋃ n ∈ B, basicNhhd n
def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}
def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n
def IsScottContinuous (f : Pomega → Pomega) : Prop :=
  ∀ x, f x = scottUnion f x
def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}
instance : TopologicalSpace Pomega :=
  .generateFrom (Set.range memOpen)
end Scott1976.DataTypesAsLattices


