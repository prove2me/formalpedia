-- Prove2me | Definitions.Def_Wowii84_LargestInducedTree
-- name    : Wowii84_LargestInducedTree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:22:32.795587+00:00
-- url     : https://prove2.me/theorems/6ecc538f-acac-41c0-ad88-52c7c1f1805d
-- title:
--   Largest Induced Tree
-- statement:
--   Definitions and structural lemmas for Largest Induced Tree, from ProblemHunter/wowii84-lean contributors and Formal Conjectures Authors (see pinned Apache-2.0 LICENSE and source headers)'s pinned Written on the Wall II Conjecture 84 on largest induced trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/LargestInducedTree.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }
end SimpleGraph


