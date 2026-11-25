-- Prove2me | Definitions.Def_IntersectionBounds_RayChaudhuriWilson
-- name    : IntersectionBounds_RayChaudhuriWilson
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:45:46.099249+00:00
-- url     : https://prove2.me/theorems/42bccb79-1e00-5f78-b39e-a325c670491e
-- title:
--   Ray Chaudhuri Wilson
-- statement:
--   Definitions and structural lemmas for Ray Chaudhuri Wilson, from Juan Pablo Traverso Gianini (jtraverso/restricted-intersections; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ray-Chaudhuri-Wilson theorem for uniform families with restricted intersections development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/RayChaudhuriWilson.lean

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V]
end IntersectionBounds


