-- Prove2me | Definitions.Def_MatchingPolytope_Defs
-- name    : MatchingPolytope_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:15:48.956589+00:00
-- url     : https://prove2.me/theorems/023da192-d3a4-515f-8643-54f012ceccdf
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Juan Pablo Traverso Gianini (jtraverso/edmonds-matching-polytope; see pinned Apache-2.0 LICENSE and source headers)'s pinned Edmonds perfect matching polytope and matching polytope theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingPolytope
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def cutEdges (S : Finset V) : Finset G.edgeSet :=
  univ.filter fun e => (∃ u ∈ (e : Sym2 V), u ∈ S) ∧ ∃ u ∈ (e : Sym2 V), u ∉ S
open Classical in
/-- The incidence vector of a subgraph's edge set. -/
noncomputable def incidence (M : G.Subgraph) : G.edgeSet → ℝ :=
  fun e => if (e : Sym2 V) ∈ M.edgeSet then 1 else 0
def perfectMatchingVectors : Set (G.edgeSet → ℝ) :=
  {x | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = incidence G M}
def edmondsPolytope : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : V, ∑ e ∈ cutEdges G {v}, x e = 1) ∧
    ∀ S : Finset V, Odd S.card → 1 ≤ ∑ e ∈ cutEdges G S, x e}
end MatchingPolytope


