-- Prove2me | Definitions.Def_Stanley_Reciprocity
-- name    : Stanley_Reciprocity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:01:37.261139+00:00
-- url     : https://prove2.me/theorems/a0717fee-6a59-4fbf-9a78-4eb6143357f1
-- title:
--   Reciprocity
-- statement:
--   Definitions and structural lemmas for Reciprocity, from Juan Pablo Traverso Gianini (jtraverso/stanley; ChromaticPolynomial/ adapted under Apache-2.0 from anlucia/ChromaticPolynomial by Angelo Lucia; see pinned LICENSE and THIRD_PARTY.md)'s pinned Stanley's acyclic orientations and chromatic reciprocity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Reciprocity.lean

module
public import Definitions.Def_Stanley_Compatible
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
end Stanley


