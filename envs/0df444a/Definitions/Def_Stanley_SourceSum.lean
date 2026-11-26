-- Prove2me | Definitions.Def_Stanley_SourceSum
-- name    : Stanley_SourceSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:55:53.583978+00:00
-- url     : https://prove2.me/theorems/d677f0b9-8900-4ae0-9e83-9ca98d876c88
-- title:
--   Source Sum
-- statement:
--   Definitions and structural lemmas for Source Sum, from Juan Pablo Traverso Gianini (jtraverso/stanley; ChromaticPolynomial/ adapted under Apache-2.0 from anlucia/ChromaticPolynomial by Angelo Lucia; see pinned LICENSE and THIRD_PARTY.md)'s pinned Stanley's acyclic orientations and chromatic reciprocity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/SourceSum.lean

module
public import Definitions.Def_Stanley_Orientation
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Stanley
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
end Stanley


