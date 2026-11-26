-- Prove2me | Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
-- name    : LeanPool_K5MinorFreeChoosability_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:05:04.702165+00:00
-- url     : https://prove2.me/theorems/b8a7a4a5-84c9-4c2c-bb89-9ce9a5468f30
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Basic.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
variable {V C : Type*}
def ListColourable (G : SimpleGraph V) (L : V → Finset C) : Prop :=
  ∃ c : G.Coloring C, ∀ v, c v ∈ L v
def ChoosableWith (G : SimpleGraph V) (C : Type*) (k : ℕ) : Prop :=
  ∀ L : V → Finset C, (∀ v, k ≤ (L v).card) → ListColourable G L
structure CliqueMinorModel (G : SimpleGraph V) (k : ℕ) where
  branch : Fin k → Finset V
  branch_nonempty : ∀ i, (branch i).Nonempty
  branch_connected : ∀ i, (G.induce (↑(branch i) : Set V)).Connected
  branch_disjoint : ∀ i j, i ≠ j → Disjoint (branch i) (branch j)
  branch_adjacent : ∀ i j, i ≠ j →
    ∃ u ∈ branch i, ∃ v ∈ branch j, G.Adj u v
def CliqueMinorFree (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ Nonempty (CliqueMinorModel G k)
end LeanPool.K5MinorFreeChoosability


