-- Prove2me | Definitions.Def_GallaiEdmondsLib_GEBarrier
-- name    : GallaiEdmondsLib_GEBarrier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:00:37.773024+00:00
-- url     : https://prove2.me/theorems/fe9f755d-49ff-55bb-ada1-310f7703c2c4
-- title:
--   GEBarrier
-- statement:
--   Definitions and structural lemmas for GEBarrier, from Juan Pablo Traverso Gianini (jtraverso/berge-matching; see pinned Apache-2.0 LICENSE and source headers)'s pinned Berge's theorem, the Tutte-Berge formula, and the Gallai-Edmonds structure theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEBarrier.lean

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
def IsBarrier (G : SimpleGraph V) (U : Set V) : Prop :=
  ∃ M : G.Subgraph, M.IsMatching ∧ M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard
def oddPart (G : SimpleGraph V) (U : Set V) : Set V := {y | y ∉ U ∧ Odd (cc G Uᶜ y).ncard}
def IsMinBarrier (G : SimpleGraph V) (U : Set V) : Prop :=
  IsBarrier G U ∧ ∀ U', IsBarrier G U' → (oddPart G U).ncard ≤ (oddPart G U').ncard
end GallaiEdmonds


