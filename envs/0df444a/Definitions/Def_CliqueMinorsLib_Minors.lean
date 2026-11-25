-- Prove2me | Definitions.Def_CliqueMinorsLib_Minors
-- name    : CliqueMinorsLib_Minors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:37:43.466953+00:00
-- url     : https://prove2.me/theorems/deb18e8d-5f0c-50c5-88d1-6da9914912c0
-- title:
--   Minors
-- statement:
--   Definitions and structural lemmas for Minors, from Juan Pablo Traverso Gianini (jtraverso/hadwiger-mader; see pinned Apache-2.0 LICENSE and source headers)'s pinned Mader's theorem and Hadwiger's conjecture for t at most 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace CliqueMinors
variable {V W : Type*}
structure MinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Finset V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_connected : ∀ w, (G.induce (↑(branch w) : Set V)).Connected
  branch_disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  branch_adjacent : ∀ w w', H.Adj w w' → ∃ u ∈ branch w, ∃ v ∈ branch w', G.Adj u v
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel G H)
section Helpers
open Relation
def InAdj (G : SimpleGraph V) (B : Finset V) (a b : V) : Prop := a ∈ B ∧ b ∈ B ∧ G.Adj a b
end Helpers
section Counting
open scoped Classical
variable [Fintype V]
end Counting
section Dirac
open scoped Classical
variable [Fintype V]
structure DiracCtx (G : SimpleGraph V) (S : Finset V) : Prop where
  supp : ∀ a b, G.Adj a b → a ∈ S
  deg : ∀ v ∈ S, 3 ≤ G.degree v
  notK4 : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G
  smaller : ∀ (G' : SimpleGraph V) (S' : Finset V), S'.card < S.card → S'.Nonempty →
    (∀ a b, G'.Adj a b → a ∈ S') → (∀ v ∈ S', 3 ≤ G'.degree v) →
    IsMinor (⊤ : SimpleGraph (Fin 4)) G'
namespace DiracCtx
variable {G : SimpleGraph V} {S : Finset V}
end DiracCtx
end Dirac
section Removal
open scoped Classical
variable [Fintype V]
end Removal
end CliqueMinors


