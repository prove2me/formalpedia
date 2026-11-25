-- Prove2me | Definitions.Def_IntersectionBounds_Separation
-- name    : IntersectionBounds_Separation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:41:34.209212+00:00
-- url     : https://prove2.me/theorems/dee8f581-9903-5db4-a7cf-a78d2ac1d8fe
-- title:
--   Separation
-- statement:
--   Definitions and structural lemmas for Separation, from Juan Pablo Traverso Gianini (jtraverso/restricted-intersections; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ray-Chaudhuri-Wilson theorem for uniform families with restricted intersections development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Separation.lean

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V)) (L : Finset K)
end IntersectionBounds


