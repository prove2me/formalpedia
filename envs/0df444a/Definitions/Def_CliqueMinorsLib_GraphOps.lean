-- Prove2me | Definitions.Def_CliqueMinorsLib_GraphOps
-- name    : CliqueMinorsLib_GraphOps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:32:44.317888+00:00
-- url     : https://prove2.me/theorems/418488c4-f9c8-401d-8a62-0283acc129b3
-- title:
--   Graph Ops
-- statement:
--   Definitions and structural lemmas for Graph Ops, from Juan Pablo Traverso Gianini (jtraverso/hadwiger-mader; see pinned Apache-2.0 LICENSE and source headers)'s pinned Mader's theorem and Hadwiger's conjecture for t at most 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace CliqueMinors
variable {V : Type*}
section GraphOps
open scoped Classical
variable [Fintype V]
def contractG (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ a ≠ y ∧ b ≠ y ∧ (G.Adj a b ∨ (a = x ∧ G.Adj y b) ∨ (b = x ∧ G.Adj y a))
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2.1, h.2.1, by
    rcases h.2.2.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
def coneG (G : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ G.Adj x a ∧ G.Adj x b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩
def opG (G : SimpleGraph V) (x b a c : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ≠ x ∧ u ≠ b ∧ v ≠ x ∧ v ≠ b ∧
    (G.Adj u v ∨ (u = a ∧ v = c) ∨ (u = c ∧ v = a))
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2.1, h.2.1, h.2.2.1, by
    rcases h.2.2.2.2.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
end GraphOps
end CliqueMinors


