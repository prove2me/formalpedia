-- Prove2me | Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
-- name    : ChromaticPolynomial_ChromaticPolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:55:40.355517+00:00
-- url     : https://prove2.me/theorems/5755be51-d9d5-4334-a967-a2e99c06fe3b
-- title:
--   Chromatic Polynomial
-- statement:
--   Definitions and structural lemmas for Chromatic Polynomial, from Juan Pablo Traverso Gianini (jtraverso/stanley; ChromaticPolynomial/ adapted under Apache-2.0 from anlucia/ChromaticPolynomial by Angelo Lucia; see pinned LICENSE and THIRD_PARTY.md)'s pinned Stanley's acyclic orientations and chromatic reciprocity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/ChromaticPolynomial/ChromaticPolynomial.lean

module
public import Definitions.Def_ChromaticPolynomial_SpanningSubgraph
public import Definitions.Def_ChromaticPolynomial_ConstantOnConnectedComponents
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Set
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
namespace SimpleGraph
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
open Classical
noncomputable instance connectedComponentFintype : Fintype G.ConnectedComponent :=
  Fintype.ofFinite _
noncomputable def edge_subset_ConnectedComponent_card (F :  {F // F ⊆ G.edgeSet}) :=
  Fintype.card ((G.spanningSubgraph_fromEdgeSet' F).coe).ConnectedComponent
variable (R: Type*) [CommRing R] [CharZero R] [NoZeroDivisors R]
@[simp]
noncomputable def ChromaticPolynomial : Polynomial R :=
  ∑ F : {F // F ⊆ G.edgeSet}, (-1)^(Fintype.card F) *
  Polynomial.X^(G.edge_subset_ConnectedComponent_card F)
variable (α : Type*) [Fintype α]
def is_proper (π : V → α) := (∀ {v w : V}, G.Adj v w → π v ≠ π w)
def coloring_equiv_coloring' : G.Coloring α ≃ {π : V → α // G.is_proper α π } where
  toFun C := ⟨C.toFun, C.valid⟩
  invFun π := Coloring.mk ↑(π) π.prop
  left_inv C := rfl
  right_inv π := by {simp; rfl}
variable (e : Sym2 V)
noncomputable def indicator_nonconstant (π : V → α) :=
  Sym2.lift ⟨fun v w => ite (π v ≠ π w) (1:R) 0, by {intros; simp_rw [ne_comm]}⟩
noncomputable def indicator_constant (π : V → α) :=
  Sym2.lift ⟨fun v w => ite (π v = π w) (1:R) 0, by {intros; simp_rw [eq_comm]}⟩
@[simp]
noncomputable def indicator_proper (π : V → α) :=
  ∏ (e ∈ G.edgeSet), (indicator_nonconstant R α π e)
open Finset
end SimpleGraph


