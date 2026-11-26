-- Prove2me | Definitions.Def_GallaiEdmondsLib_GEMatching
-- name    : GallaiEdmondsLib_GEMatching
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:58:30.107279+00:00
-- url     : https://prove2.me/theorems/28445114-31d8-5780-87e9-8d46d7cecc2c
-- title:
--   GEMatching
-- statement:
--   Definitions and structural lemmas for GEMatching, from Juan Pablo Traverso Gianini (jtraverso/berge-matching; see pinned Apache-2.0 LICENSE and source headers)'s pinned Berge's theorem, the Tutte-Berge formula, and the Gallai-Edmonds structure theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEMatching.lean

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
open Classical in
/-- The partner of a vertex in a matching. -/
noncomputable def partner {M : G.Subgraph} (hM : M.IsMatching) (y : V) : V :=
  if h : y ∈ M.verts then (hM h).choose else y
end GallaiEdmonds


