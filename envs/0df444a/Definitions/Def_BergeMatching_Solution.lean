-- Prove2me | Definitions.Def_BergeMatching_Solution
-- name    : BergeMatching_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:06:36.707826+00:00
-- url     : https://prove2.me/theorems/a564850e-43b5-475b-b805-ee5e3e833245
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/berge-matching; see pinned Apache-2.0 LICENSE and source headers)'s pinned Berge's theorem, the Tutte-Berge formula, and the Gallai-Edmonds structure theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace BergeTheorem
variable {V : Type*}
noncomputable def oddCount (G : SimpleGraph V) (U : Set V) : ℕ :=
  ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard
def IsAugmentingPath {G : SimpleGraph V} (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ u ≠ v ∧ u ∉ M.verts ∧ v ∉ M.verts ∧
    ∀ i < p.length, (s(p.getVert i, p.getVert (i + 1)) ∈ M.edgeSet ↔ Odd i)
end BergeTheorem
namespace GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
end GallaiEdmondsTheorem


