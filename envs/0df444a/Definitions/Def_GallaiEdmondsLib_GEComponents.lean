-- Prove2me | Definitions.Def_GallaiEdmondsLib_GEComponents
-- name    : GallaiEdmondsLib_GEComponents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:56:34.746281+00:00
-- url     : https://prove2.me/theorems/57e55fc8-fa54-44f6-9bb0-4acacd8a3dbd
-- title:
--   GEComponents
-- statement:
--   Definitions and structural lemmas for GEComponents, from Juan Pablo Traverso Gianini (jtraverso/berge-matching; see pinned Apache-2.0 LICENSE and source headers)'s pinned Berge's theorem, the Tutte-Berge formula, and the Gallai-Edmonds structure theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace GallaiEdmonds
variable {V : Type*}
def cc (G : SimpleGraph V) (W : Set V) (x : V) : Set V :=
  {y | ∃ (hx : x ∈ W) (hy : y ∈ W), (G.induce W).Reachable ⟨x, hx⟩ ⟨y, hy⟩}
def comps (G : SimpleGraph V) (W : Set V) : Set (Set V) := {S | ∃ x ∈ W, S = cc G W x}
def oddComps (G : SimpleGraph V) (W : Set V) : Set (Set V) :=
  {S | S ∈ comps G W ∧ Odd S.ncard}
noncomputable def oddC (G : SimpleGraph V) (W : Set V) : ℕ := (oddComps G W).ncard
def restrictG (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.1 _ h.1⟩
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
def Closed (G : SimpleGraph V) (W W' : Set V) : Prop := ∀ y ∈ W', ∀ z ∈ W, G.Adj y z → z ∈ W'
end GallaiEdmonds


