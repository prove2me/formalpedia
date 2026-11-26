-- Prove2me | Definitions.Def_ChromaticPolynomial_ConstantOnConnectedComponents
-- name    : ChromaticPolynomial_ConstantOnConnectedComponents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:55:19.262806+00:00
-- url     : https://prove2.me/theorems/3fd07d40-6fcd-5aa4-8fdb-cdef7fb894d8
-- title:
--   Constant On Connected Components
-- statement:
--   Definitions and structural lemmas for Constant On Connected Components, from Juan Pablo Traverso Gianini (jtraverso/stanley; ChromaticPolynomial/ adapted under Apache-2.0 from anlucia/ChromaticPolynomial by Angelo Lucia; see pinned LICENSE and THIRD_PARTY.md)'s pinned Stanley's acyclic orientations and chromatic reciprocity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/ChromaticPolynomial/ConstantOnConnectedComponents.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
namespace SimpleGraph
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
variable {α : Type*} [Fintype α]
open Classical
omit [Fintype V] [Fintype α] in
lemma constant_on_cc (π : V → α) : (∀ {v w : V}, G.Adj v w → π v = π w) ↔
  (∀ (v w : V) (p : G.Walk v w), p.IsPath → π v = π w) := by
  constructor
  · intro hconstant _ _ walk hpath
    induction walk with
    | nil => rfl
    | cons h p ih =>
      rw [hconstant h]
      exact ih (Walk.IsPath.of_cons hpath)
  · intro hpath v w hadj
    have p := (Adj.toWalk hadj).toPath
    exact hpath v w p p.prop
def equiv_constant_on_cc :
  {π : V → α // ∀ {v w : V}, G.Adj v w → π v = π w } ≃ (G.ConnectedComponent → α) where
  toFun π := ConnectedComponent.lift π.val ((G.constant_on_cc π.val).mp π.prop)
  invFun P := ⟨fun v ↦ P (G.connectedComponentMk v), by {
    intro v w hadj
    simp
    rw [ConnectedComponent.connectedComponentMk_eq_of_adj hadj]
  }⟩
  left_inv _ := by simp
  right_inv P := by
    simp
    apply funext_iff.mpr
    intro c
    induction c using Quot.induction_on with
    | _ v => rfl
end SimpleGraph


