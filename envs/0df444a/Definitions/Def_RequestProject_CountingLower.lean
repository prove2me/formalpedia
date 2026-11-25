-- Prove2me | Definitions.Def_RequestProject_CountingLower
-- name    : RequestProject_CountingLower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:40:29.314657+00:00
-- url     : https://prove2.me/theorems/acbbb315-2440-4dae-841d-f88f9fff59df
-- title:
--   Counting Lower
-- statement:
--   Definitions and structural lemmas for Counting Lower, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CountingLower.lean

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Truncation
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
section LeafExtTree
variable {K : Type*} [Fintype K] {S : SimpleGraph K} {m : K → ℕ}
lemma leafExt_degree_inl (x : K) : (leafExt S m).degree (.inl x) = S.degree x + m x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter, SimpleGraph.neighborFinset_eq_filter, card_filter,
    card_filter, Fintype.sum_sum_type, Fintype.sum_sigma]
  congr 1
  simp only [leafExt_adj_inl_inr]
  rw [sum_eq_single x]
  · simp
  · intro b _ hb; simp [hb]
  · simp
lemma leafExt_degree_inr (l : Σ i, Fin (m i)) : (leafExt S m).degree (.inr l) = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    card_eq_one]
  refine ⟨.inl l.1, ?_⟩
  ext y
  rcases y with i | l'
  · simp [eq_comm]
  · simp
lemma leafExt_card_edgeFinset (hS : S.IsTree) :
    (leafExt S m).edgeFinset.card + 1 = Fintype.card K + ∑ i, m i := by
  have h1 := (leafExt S m).sum_degrees_eq_twice_card_edges
  have h2 := S.sum_degrees_eq_twice_card_edges
  have h3 := hS.card_edgeFinset
  rw [Fintype.sum_sum_type] at h1
  simp only [leafExt_degree_inl, leafExt_degree_inr, sum_add_distrib, sum_const, card_univ,
    Fintype.card_sigma, Fintype.card_fin, smul_eq_mul, mul_one] at h1
  omega
lemma leafExt_isTree (hS : S.IsTree) : (leafExt S m).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · obtain ⟨x0⟩ := hS.1.nonempty
    haveI : Nonempty (K ⊕ Σ i, Fin (m i)) := ⟨.inl x0⟩
    let f : S →g leafExt S m := ⟨Sum.inl, fun h => h⟩
    have hinl : ∀ y, (leafExt S m).Reachable (.inl x0) (.inl y) :=
      fun y => (hS.1.preconnected x0 y).map f
    have hall : ∀ v, (leafExt S m).Reachable (.inl x0) v := by
      rintro (y | l)
      · exact hinl y
      · exact (hinl l.1).trans (SimpleGraph.Adj.reachable (by simp))
    exact ⟨fun u v => (hall u).symm.trans (hall v)⟩
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card,
      leafExt_card_edgeFinset hS, Fintype.card_sum, Fintype.card_sigma]
    simp
end LeafExtTree
lemma bot_unit_isTree : (⊥ : SimpleGraph Unit).IsTree :=
  ⟨⟨fun u v => by rw [Subsingleton.elim u v]⟩, SimpleGraph.isAcyclic_bot⟩
def starTree (r : ℕ) := leafExt (⊥ : SimpleGraph Unit) (fun _ => r)
def famWeights (r : ℕ) (A : Finset ℕ) : Unit ⊕ (Σ _ : Unit, Fin r) → ℕ
  | .inl _ => 0
  | .inr l => if (l.2 : ℕ) ∈ A then l.2 else 0
def famTree (r : ℕ) (A : Finset ℕ) := leafExt (starTree r) (famWeights r A)
lemma famTree_isTree (r : ℕ) (A : Finset ℕ) : (famTree r A).IsTree :=
  leafExt_isTree (leafExt_isTree bot_unit_isTree)
lemma famTree_card (r : ℕ) (A : Finset ℕ) (hA : A ⊆ range r) :
    Fintype.card ((Unit ⊕ (Σ _ : Unit, Fin r)) ⊕ Σ x, Fin (famWeights r A x)) =
      1 + r + ∑ i ∈ A, i := by
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.sum_sum_type, Fintype.card_sum,
    Fintype.card_sigma]
  simp only [Fintype.card_unit, Fintype.card_fin]
  simp only [Fintype.card_unit, sum_const, card_univ, smul_eq_mul,
    famWeights, Fintype.sum_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ∈ A then j else 0), ← sum_filter,
    filter_mem_eq_inter, inter_eq_right.2 hA]
  simp
instance (k : ℕ) : Finite (TreeClass k) := Quotient.finite _
def famTreeFin (k : ℕ) (A : Finset ℕ) (hA : A ⊆ range (k - 1 - ∑ i ∈ A, i))
    (hk : ∑ i ∈ A, i + 1 ≤ k) : {S : SimpleGraph (Fin k) // S.IsTree} :=
  let e := Fintype.equivFinOfCardEq (by rw [famTree_card _ A hA]; omega :
    Fintype.card ((Unit ⊕ (Σ _ : Unit, Fin (k - 1 - ∑ i ∈ A, i))) ⊕
      Σ x, Fin (famWeights (k - 1 - ∑ i ∈ A, i) A x)) = k)
  ⟨(famTree (k - 1 - ∑ i ∈ A, i) A).map e.toEmbedding,
    (SimpleGraph.Iso.map e _).isTree_iff.1 (famTree_isTree _ A)⟩
end ChromaticReconstruction


