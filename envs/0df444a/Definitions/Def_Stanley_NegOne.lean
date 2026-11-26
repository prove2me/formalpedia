-- Prove2me | Definitions.Def_Stanley_NegOne
-- name    : Stanley_NegOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:56:36.683983+00:00
-- url     : https://prove2.me/theorems/d605c3c2-ebae-5ce5-8053-8e6b78fdb45e
-- title:
--   Neg One
-- statement:
--   Definitions and structural lemmas for Neg One, from Juan Pablo Traverso Gianini (jtraverso/stanley; ChromaticPolynomial/ adapted under Apache-2.0 from anlucia/ChromaticPolynomial by Angelo Lucia; see pinned LICENSE and THIRD_PARTY.md)'s pinned Stanley's acyclic orientations and chromatic reciprocity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/NegOne.lean

module
public import Definitions.Def_Stanley_Convolution
public import Mathlib.Tactic.NormNum
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
end Stanley


