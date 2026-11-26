-- Prove2me | Definitions.Def_BergeLib_Berge
-- name    : BergeLib_Berge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:52:23.116059+00:00
-- url     : https://prove2.me/theorems/ca231489-db79-4336-8bb9-44f3fc1c344f
-- title:
--   Berge
-- statement:
--   Definitions and structural lemmas for Berge, from Juan Pablo Traverso Gianini (jtraverso/berge-matching; see pinned Apache-2.0 LICENSE and source headers)'s pinned Berge's theorem, the Tutte-Berge formula, and the Gallai-Edmonds structure theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/BergeLib/Berge.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace BergeMatching
variable {V : Type*}
noncomputable def oddCount (G : SimpleGraph V) (U : Set V) : ℕ :=
  ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard
def IsAugmentingPath {G : SimpleGraph V} (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ u ≠ v ∧ u ∉ M.verts ∧ v ∉ M.verts ∧
    ∀ i < p.length, (s(p.getVert i, p.getVert (i + 1)) ∈ M.edgeSet ↔ Odd i)
def aug (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj x y := x ≠ y ∧ ∀ a b, x = .inl a → y = .inl b → G.Adj a b
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun a b hx hy => (h.2 b a hy hx).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
@[simp] lemma aug_adj_inl_inl {G : SimpleGraph V} {d : ℕ} {a b : V} :
    (aug G d).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  change _ ∧ _ ↔ _
  refine ⟨fun h => h.2 a b rfl rfl, fun h => ⟨fun h' => h.ne (Sum.inl_injective h'), ?_⟩⟩
  rintro a' b' ha hb
  cases ha; cases hb; exact h
def augSet (U : Set V) (d : ℕ) : Set (V ⊕ Fin d) := Sum.inl '' U ∪ Set.range Sum.inr
def liftSub {G : SimpleGraph V} (M : G.Subgraph) (d : ℕ) : (aug G d).Subgraph where
  verts := Sum.inl '' M.verts
  Adj x y := ∃ a b, x = .inl a ∧ y = .inl b ∧ M.Adj a b
  adj_sub := by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact aug_adj_inl_inl.2 (M.adj_sub h)
  edge_vert := by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact ⟨a, M.edge_vert h, rfl⟩
  symm := ⟨by
    rintro _ _ ⟨a, b, rfl, rfl, h⟩
    exact ⟨b, a, rfl, rfl, h.symm⟩⟩
section BergeHelpers
variable {G : SimpleGraph V}
end BergeHelpers
end BergeMatching


