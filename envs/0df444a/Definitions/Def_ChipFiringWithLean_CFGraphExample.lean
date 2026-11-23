-- Prove2me | Definitions.Def_ChipFiringWithLean_CFGraphExample
-- name    : ChipFiringWithLean_CFGraphExample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:48:32.660533+00:00
-- url     : https://prove2.me/theorems/2d029830-7293-4d79-9c91-c006bdebabaa
-- title:
--   CFGraph Example
-- statement:
--   Definitions and structural lemmas for CFGraph Example, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/CFGraphExample.lean

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
inductive Person : Type
  | A | B | C | E
  deriving DecidableEq
instance : Fintype Person where
  elems := {Person.A, Person.B, Person.C, Person.E}
  complete := by
    intro x
    cases x <;> simp only [mem_insert, reduceCtorEq, Finset.mem_singleton, or_false, or_true,
        or_self]
instance : Nonempty Person := ⟨Person.A⟩
def exampleEdges : Multiset (Person × Person) :=
  Multiset.ofList [
    (Person.A, Person.B),
    (Person.B, Person.C),
    (Person.C, Person.E)
  ]
def edgesWithLoop : Multiset (Person × Person) :=
  Multiset.ofList [
    (Person.A, Person.B),
    (Person.A, Person.A),   -- This is a loop
    (Person.B, Person.C),
  ]
def example_graph : CFGraph := {
  V := Person,
  edges := Multiset.ofList [
    (Person.A, Person.B), (Person.B, Person.C),
    (Person.A, Person.C), (Person.A, Person.E),
    (Person.A, Person.E), (Person.E, Person.C)
  ],
  loopless := by decide,
}
def initial_wealth : CFDiv example_graph :=
  fun v => match v with
  | Person.A => 2
  | Person.B => -3
  | Person.C => 4
  | Person.E => -1
def after_charlie_lends := firing_move example_graph initial_wealth Person.C
def W₁ : Finset example_graph.V := {Person.A, Person.E, Person.C}
def after_W₁_firing := set_firing example_graph initial_wealth W₁
def W₂ : Finset example_graph.V := W₁
def after_W₂_firing := set_firing example_graph after_W₁_firing W₂
def W₃ : Finset example_graph.V := {Person.B, Person.C}
def after_W₃_firing := set_firing example_graph after_W₂_firing W₃
def after_bob_borrows := borrowing_move example_graph initial_wealth Person.B
def example_laplacian := laplacian_matrix example_graph
def firing_script_example : firing_script example_graph := fun v => match v with
  | Person.A => 0
  | Person.B => -1
  | Person.C => 1
  | Person.E => 0
def res_div_post_lap_based_script_firing := apply_laplacian example_graph firing_script_example initial_wealth
def non_q_reduced_example : CFDiv example_graph := fun v => match v with
  | Person.A => 1
  | Person.B => -1  -- violates non-negativity condition for non-q vertices
  | Person.C => 2
  | Person.E => 1


