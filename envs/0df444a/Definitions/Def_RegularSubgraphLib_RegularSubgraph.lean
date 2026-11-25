-- Prove2me | Definitions.Def_RegularSubgraphLib_RegularSubgraph
-- name    : RegularSubgraphLib_RegularSubgraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:19:02.909681+00:00
-- url     : https://prove2.me/theorems/f947b580-94f6-4a5f-822a-29620c6d11f7
-- title:
--   Regular Subgraph
-- statement:
--   Definitions and structural lemmas for Regular Subgraph, from Juan Pablo Traverso Gianini (jtraverso/regular-subgraphs; see pinned Apache-2.0 LICENSE and source headers)'s pinned Regular subgraphs of almost regular graphs (Alon-Friedland-Kalai) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph MvPolynomial Finset
namespace RegularSubgraph
variable {V : Type*} [Fintype V]
section ChevalleyWarning
variable (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ)
abbrev Edge : Type _ := G.edgeSet
noncomputable def val (x : Edge G → ZMod p) (a b : V) : ZMod p :=
  if h : G.Adj a b then x ⟨s(a, b), h⟩ else 0
noncomputable def var (a b : V) : MvPolynomial (Edge G) (ZMod p) :=
  if h : G.Adj a b then X ⟨s(a, b), h⟩ else 0
noncomputable def poly (v : V) : MvPolynomial (Edge G) (ZMod p) :=
  ∑ w, var G p v w ^ (p - 1)
variable {G p}
variable [hp : Fact p.Prime]
end ChevalleyWarning
end RegularSubgraph


