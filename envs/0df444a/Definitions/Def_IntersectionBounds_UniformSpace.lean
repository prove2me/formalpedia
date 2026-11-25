-- Prove2me | Definitions.Def_IntersectionBounds_UniformSpace
-- name    : IntersectionBounds_UniformSpace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:41:38.562263+00:00
-- url     : https://prove2.me/theorems/3328d26b-f24e-5ce9-9bf3-12b6841f62b0
-- title:
--   Uniform Space
-- statement:
--   Definitions and structural lemmas for Uniform Space, from Juan Pablo Traverso Gianini (jtraverso/restricted-intersections; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ray-Chaudhuri-Wilson theorem for uniform families with restricted intersections development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/UniformSpace.lean

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Definitions
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V] {K : Type v} [Field K]
variable (F : Finset (Finset V))
end IntersectionBounds


