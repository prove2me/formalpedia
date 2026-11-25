-- Prove2me | Definitions.Def_TreePackingLib_NashWilliamsAux
-- name    : TreePackingLib_NashWilliamsAux
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:35:55.663002+00:00
-- url     : https://prove2.me/theorems/08e4c918-694b-41df-aac4-2bed6cc80ffd
-- title:
--   Nash Williams Aux
-- statement:
--   Definitions and structural lemmas for Nash Williams Aux, from Juan Pablo Traverso Gianini (jtraverso/nash-williams-trees; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Nash-Williams-Tutte tree packing theorem and Nash-Williams' arboricity theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Fintype SimpleGraph Function
namespace NashWilliams
variable {V : Type*}
theorem disjoint_iff_adj {A B : SimpleGraph V} :
    Disjoint A B ↔ ∀ a b, A.Adj a b → ¬ B.Adj a b := by
  rw [← disjoint_edgeSet, Set.disjoint_left]
  constructor
  · intro h a b ha hb
    exact h (show s(a, b) ∈ A.edgeSet from ha) hb
  · intro h e
    induction e using Sym2.ind with
    | _ a b => exact fun ha hb ↦ h a b ha hb
section Exchange
variable (G : SimpleGraph V) {k : ℕ}
def Valid (F : Fin k → SimpleGraph V) : Prop :=
  (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ Pairwise fun i j ↦ Disjoint (F i) (F j)
noncomputable def total (F : Fin k → SimpleGraph V) : ℕ := ∑ i, (F i).edgeSet.ncard
def Uncov (F : Fin k → SimpleGraph V) (u v : V) : Prop := G.Adj u v ∧ ∀ j, ¬ (F j).Adj u v
def Step (F F' : Fin k → SimpleGraph V) : Prop :=
  ∃ i u v x y, Uncov G F u v ∧ (F i).Adj x y ∧
    ((F i).deleteEdges {s(x, y)} ⊔ edge u v).IsAcyclic ∧
    F' = update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)
variable {G}
theorem Valid.update {F : Fin k → SimpleGraph V} (hF : Valid G F) (i : Fin k) {X : SimpleGraph V}
    (hXG : X ≤ G) (hX : X.IsAcyclic)
    (hXadj : ∀ a b, X.Adj a b → (F i).Adj a b ∨ ∀ j, ¬ (F j).Adj a b) :
    Valid G (update F i X) := by
  refine ⟨fun j ↦ ?_, fun j₁ j₂ hj ↦ ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using ⟨hXG, hX⟩
    · simpa [hj] using hF.1 j
  · have key : ∀ j, j ≠ i → Disjoint X (F j) := by
      intro j hji
      rw [disjoint_iff_adj]
      intro a b hab
      rcases hXadj a b hab with h | h
      · exact (disjoint_iff_adj.1 (hF.2 (Ne.symm hji))) a b h
      · exact h j
    by_cases h₁ : j₁ = i
    · subst h₁
      simpa [Ne.symm hj] using key j₂ (Ne.symm hj)
    · by_cases h₂ : j₂ = i
      · subst h₂
        simpa [h₁] using (key j₁ h₁).symm
      · simpa [h₁, h₂] using hF.2 hj
end Exchange
section Core
variable {G : SimpleGraph V} {k : ℕ}
def exchGraph (G : SimpleGraph V) (F₀ : Fin k → SimpleGraph V) : SimpleGraph V where
  Adj a b := ∃ F, Relation.ReflTransGen (Step G) F₀ F ∧ Uncov G F a b
  symm := ⟨fun _ _ ⟨F, h, hu⟩ ↦ ⟨F, h, hu.1.symm, fun j h' ↦ hu.2 j h'.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, hu⟩ ↦ hu.1.ne rfl⟩
variable [Finite V] {F₀ : Fin k → SimpleGraph V} (hF₀ : Valid G F₀)
  (hmax : ∀ F : Fin k → SimpleGraph V, Valid G F → total F ≤ total F₀)
include hF₀ hmax
end Core
end NashWilliams


