-- Prove2me | Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
-- name    : MatchingPolytope_PerfectMatchingPolytope
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:27:07.418021+00:00
-- url     : https://prove2.me/theorems/dcd0affe-8dde-5008-b2ce-d975c998b82b
-- title:
--   Perfect Matching Polytope
-- statement:
--   Definitions and structural lemmas for Perfect Matching Polytope, from Juan Pablo Traverso Gianini (jtraverso/edmonds-matching-polytope; see pinned Apache-2.0 LICENSE and source headers)'s pinned Edmonds perfect matching polytope and matching polytope theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingPolytope
open Finset Multi
section Convexity
variable {V E : Type*}
end Convexity
section Subgraph
variable {V : Type*} (G : SimpleGraph V)
def subgraphOf (M : Finset G.edgeSet) : G.Subgraph where
  verts := Set.univ
  Adj a b := ∃ e ∈ M, (e : Sym2 V) = s(a, b)
  adj_sub := by
    rintro a b ⟨e, -, he⟩
    have := e.2
    rw [he] at this
    exact (SimpleGraph.mem_edgeSet G).1 this
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨by
    rintro a b ⟨e, he, h⟩
    exact ⟨e, he, h.trans Sym2.eq_swap⟩⟩
end Subgraph
section
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
abbrev edgeEnds : G.edgeSet → Sym2 V := fun e => (e : Sym2 V)
open Classical in
/-- The edges of a subgraph, as a finset of edges of `G`. -/
noncomputable def edgesOf (M : G.Subgraph) : Finset G.edgeSet :=
  univ.filter fun e => (e : Sym2 V) ∈ M.edgeSet
end
end MatchingPolytope


