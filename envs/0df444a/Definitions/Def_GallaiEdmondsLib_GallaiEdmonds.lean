-- Prove2me | Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
-- name    : GallaiEdmondsLib_GallaiEdmonds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:04:32.545806+00:00
-- url     : https://prove2.me/theorems/a3d5ab57-397e-45a4-a375-ba72310e8b3b
-- title:
--   Gallai Edmonds
-- statement:
--   Definitions and structural lemmas for Gallai Edmonds, from Juan Pablo Traverso Gianini (jtraverso/berge-matching; see pinned Apache-2.0 LICENSE and source headers)'s pinned Berge's theorem, the Tutte-Berge formula, and the Gallai-Edmonds structure theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GallaiEdmonds.lean

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
def IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard
def setD : Set V := {v | ∃ M : G.Subgraph, IsMaximumMatching G M ∧ v ∉ M.verts}
def setA : Set V := {v | v ∉ setD G ∧ ∃ u ∈ setD G, G.Adj u v}
def setC : Set V := {v | v ∉ setD G ∧ v ∉ setA G}
def HasPerfectMatchingOn (S : Set V) : Prop :=
  ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = S
def compSet (c : (G.induce (setD G)).ConnectedComponent) : Set V :=
  {v | ∃ h : v ∈ setD G, (G.induce (setD G)).connectedComponentMk ⟨v, h⟩ = c}
end GallaiEdmonds


