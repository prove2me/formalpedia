-- Prove2me | Definitions.Def_RequestProject_ProperTree
-- name    : RequestProject_ProperTree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:06:03.92468+00:00
-- url     : https://prove2.me/theorems/d66bbbd7-50e9-4e1b-8d04-7a351e4923fd
-- title:
--   Proper Tree
-- statement:
--   Definitions and structural lemmas for Proper Tree, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/ProperTree.lean

import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_card_le_two_of_adj_leaves
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_neighborFinset_eq_of_degree_one
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
def leafExtIso {K K' : Type*} {S : SimpleGraph K} {S' : SimpleGraph K'} {m : K → ℕ}
    {m' : K' → ℕ} (φ : S ≃g S') (hm : ∀ x, m' (φ x) = m x) : leafExt S m ≃g leafExt S' m' where
  toEquiv := Equiv.sumCongr φ.toEquiv (Equiv.sigmaCongr φ.toEquiv fun i => finCongr (hm i).symm)
  map_rel_iff' := by
    intro a b
    rcases a with i | ⟨i, t⟩ <;> rcases b with j | ⟨j, s⟩
    · exact φ.map_rel_iff'
    · show (leafExt S' m').Adj (.inl (φ i)) (.inr ⟨φ j, _⟩) ↔ _
      simp only [leafExt_adj_inl_inr]
      exact φ.injective.eq_iff
    · show (leafExt S' m').Adj (.inr ⟨φ i, _⟩) (.inl (φ j)) ↔ _
      simp only [leafExt_adj_inr_inl]
      exact φ.injective.eq_iff
    · show (leafExt S' m').Adj (.inr _) (.inr _) ↔ _
      simp only [leafExt_adj_inr_inr]
variable {V : Type*} [Fintype V] {T : SimpleGraph V}
def leafNbrs (T : SimpleGraph V) (c : SkelVert T) : Finset V :=
  univ.filter fun u => T.Adj c.1 u ∧ IsLeaf T u
def leafCount (T : SimpleGraph V) (c : SkelVert T) : ℕ := (leafNbrs T c).card
lemma eq_of_adj_leaf {u c c' : V} (hu : IsLeaf T u) (h1 : T.Adj u c) (h2 : T.Adj u c') :
    c = c' := by
  have := neighborFinset_eq_of_degree_one hu h1
  have h2' := (T.mem_neighborFinset u c').2 h2
  rw [this, mem_singleton] at h2'
  exact h2'.symm
lemma not_leaf_of_adj_leaf (hT : IsProperTree T) {u c : V} (hu : IsLeaf T u) (h : T.Adj u c) :
    ¬ IsLeaf T c := fun hc => by
  have := card_le_two_of_adj_leaves hT.1.1 h hu hc
  have := hT.2.1
  omega
lemma exists_adj_of_leaf {u : V} (hu : IsLeaf T u) : ∃ c, T.Adj u c := by
  have : (T.neighborFinset u).Nonempty := by
    rw [← card_pos, SimpleGraph.card_neighborFinset_eq_degree]
    unfold IsLeaf at hu
    omega
  obtain ⟨c, hc⟩ := this
  exact ⟨c, (T.mem_neighborFinset u c).1 hc⟩
def properMap (T : SimpleGraph V) : SkelVert T ⊕ (Σ c, Fin (leafCount T c)) → V
  | .inl c => c.1
  | .inr ⟨c, j⟩ => ((leafNbrs T c).equivFin.symm j).1
lemma properMap_inr_mem (c : SkelVert T) (j : Fin (leafCount T c)) :
    properMap T (.inr ⟨c, j⟩) ∈ leafNbrs T c :=
  ((leafNbrs T c).equivFin.symm j).2
lemma properMap_inr_adj (c : SkelVert T) (j : Fin (leafCount T c)) :
    T.Adj c.1 (properMap T (.inr ⟨c, j⟩)) ∧ IsLeaf T (properMap T (.inr ⟨c, j⟩)) := by
  have := properMap_inr_mem c j
  simpa [leafNbrs] using this
lemma properMap_injective : Function.Injective (properMap T) := by
  rintro (c | ⟨c, j⟩) (c' | ⟨c', j'⟩) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · have := (properMap_inr_adj c' j').2
    rw [← h] at this
    exact absurd this c.2
  · have := (properMap_inr_adj c j).2
    rw [h] at this
    exact absurd this c'.2
  · have h1 := properMap_inr_adj c j
    have h2 := properMap_inr_adj c' j'
    rw [h] at h1
    obtain rfl : c = c' := Subtype.ext (eq_of_adj_leaf h1.2 h1.1.symm h2.1.symm)
    have : j = j' := by
      have := (leafNbrs T c).equivFin.symm.injective (Subtype.ext h)
      exact this
    rw [this]
lemma properMap_surjective (hT : IsProperTree T) : Function.Surjective (properMap T) := by
  intro v
  by_cases hv : IsLeaf T v
  · obtain ⟨c, hc⟩ := exists_adj_of_leaf hv
    let C : SkelVert T := ⟨c, not_leaf_of_adj_leaf hT hv hc⟩
    have hmem : v ∈ leafNbrs T C := by simp [leafNbrs, C, hc.symm, hv]
    refine ⟨.inr ⟨C, (leafNbrs T C).equivFin ⟨v, hmem⟩⟩, ?_⟩
    simp [properMap]
  · exact ⟨.inl ⟨v, hv⟩, rfl⟩
lemma properMap_adj (hT : IsProperTree T) (x y : SkelVert T ⊕ (Σ c, Fin (leafCount T c))) :
    T.Adj (properMap T x) (properMap T y) ↔ (leafExt (skeleton T) (leafCount T)).Adj x y := by
  rcases x with c | ⟨c, j⟩ <;> rcases y with c' | ⟨c', j'⟩
  · exact Iff.rfl
  · rw [leafExt_adj_inl_inr]
    have h2 := properMap_inr_adj c' j'
    constructor
    · intro h
      exact Subtype.ext (eq_of_adj_leaf h2.2 h2.1.symm h.symm)
    · rintro rfl
      exact h2.1
  · rw [leafExt_adj_inr_inl]
    have h2 := properMap_inr_adj c j
    constructor
    · intro h
      exact Subtype.ext (eq_of_adj_leaf h2.2 h2.1.symm h)
    · rintro rfl
      exact h2.1.symm
  · simp only [leafExt_adj_inr_inr, iff_false]
    intro h
    exact not_leaf_of_adj_leaf hT (properMap_inr_adj c j).2 h (properMap_inr_adj c' j').2
def properIso (hT : IsProperTree T) : leafExt (skeleton T) (leafCount T) ≃g T where
  toEquiv := Equiv.ofBijective (properMap T) ⟨properMap_injective, properMap_surjective hT⟩
  map_rel_iff' := properMap_adj hT _ _
end ChromaticReconstruction


