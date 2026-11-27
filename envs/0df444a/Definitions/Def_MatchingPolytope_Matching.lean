-- Prove2me | Definitions.Def_MatchingPolytope_Matching
-- name    : MatchingPolytope_Matching
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:30:13.759975+00:00
-- url     : https://prove2.me/theorems/f019e457-dd3d-4d8e-8a8b-ff68d8b00888
-- title:
--   Matching
-- statement:
--   Definitions and structural lemmas for Matching, from Juan Pablo Traverso Gianini (jtraverso/edmonds-matching-polytope; see pinned Apache-2.0 LICENSE and source headers)'s pinned Edmonds perfect matching polytope and matching polytope theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Matching.lean

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def innerEdges (S : Finset V) : Finset G.edgeSet :=
  univ.filter fun e => ∀ u ∈ (e : Sym2 V), u ∈ S
def matchingVectors : Set (G.edgeSet → ℝ) :=
  {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = incidence G M}
def matchingPolytope : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : V, ∑ e ∈ cutEdges G {v}, x e ≤ 1) ∧
    ∀ S : Finset V, Odd S.card → ∑ e ∈ innerEdges G S, x e ≤ ((S.card : ℝ) - 1) / 2}
section Subgraph
variable {V : Type*} (G : SimpleGraph V)
def matchingSubgraphOf (M : Finset G.edgeSet) : G.Subgraph where
  verts := {v | ∃ w, ∃ e ∈ M, (e : Sym2 V) = s(v, w)}
  Adj a b := ∃ e ∈ M, (e : Sym2 V) = s(a, b)
  adj_sub := by
    rintro a b ⟨e, -, he⟩
    have := e.2
    rw [he] at this
    exact (SimpleGraph.mem_edgeSet G).1 this
  edge_vert := fun h => ⟨_, h⟩
  symm := ⟨by
    rintro a b ⟨e, he, h⟩
    exact ⟨e, he, h.trans Sym2.eq_swap⟩⟩
end Subgraph
section Fin
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
end Fin
abbrev DEdge := G.edgeSet ⊕ (G.edgeSet ⊕ V)
def dEnds : DEdge G → Sym2 (V ⊕ V)
  | Sum.inl e => (e : Sym2 V).map Sum.inl
  | Sum.inr (Sum.inl e) => (e : Sym2 V).map Sum.inr
  | Sum.inr (Sum.inr v) => s(Sum.inl v, Sum.inr v)
def dvec (x : G.edgeSet → ℝ) : DEdge G → ℝ
  | Sum.inl e => x e
  | Sum.inr (Sum.inl e) => x e
  | Sum.inr (Sum.inr v) => 1 - ∑ e ∈ cutEdges G {v}, x e
noncomputable def proj (N : Finset (DEdge G)) : Finset G.edgeSet := by
  classical exact univ.filter fun e => Sum.inl e ∈ N
end MatchingPolytope


