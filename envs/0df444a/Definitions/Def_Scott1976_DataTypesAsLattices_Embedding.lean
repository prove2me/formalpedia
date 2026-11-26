-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
-- name    : Scott1976_DataTypesAsLattices_Embedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:53:42.572136+00:00
-- url     : https://prove2.me/theorems/04c9f90f-e436-42d8-86b9-be6b86e58a2a
-- title:
--   Embedding
-- statement:
--   Definitions and structural lemmas for Embedding, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Embedding.lean

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
open TopologicalSpace
def extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (y : Y) : Pomega :=
  ⋃₀ { t | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ t = ⋂₀ (f '' {x : X | ↑x ∈ U}) }
def embed {X : Type*} (U : ℕ → Set X) (x : X) : Pomega :=
  {n | x ∈ U n}
end Scott1976.DataTypesAsLattices


