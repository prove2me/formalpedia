-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:19:45.022218+00:00
-- url     : https://prove2.me/theorems/ea993013-228d-400e-9dfa-591622beff90
-- title:
--   TernaryPartitionCount
-- statement:
--   Definitions and structural lemmas for TernaryPartitionCount, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPartitionCount.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Mathlib.Tactic
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_count_total
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound
abbrev Index (t r s : ℕ) := Fin t ⊕ (Fin (2*r) ⊕ Fin (3*s))
abbrev Parts (r s : ℕ) := {S // S ∈ LayerCounts.vertices (2*r) r} × LocalGraph.Edge (3*s) s
def piType (t r s : ℕ) : DigitType := ![t,2*r,3*s]
def alphaType (t r s : ℕ) : DigitType := ![t+r+s,r+s,s]
abbrev partLeft {t r s : ℕ} (c : Parts r s) : Index t r s → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => if i ∈ c.1.val then 1 else 0
  | Sum.inr (Sum.inr i) => if i ∈ c.2.val.1 then 0 else if i ∈ c.2.val.2 then 2 else 1
abbrev partRight {t r s : ℕ} (c : Parts r s) : Index t r s → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => if i ∈ c.1.val then 0 else 1
  | Sum.inr (Sum.inr i) => if i ∈ c.2.val.1 then 2 else if i ∈ c.2.val.2 then 0 else 1
abbrev targetWord (t r s : ℕ) : Index t r s → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2
theorem left_indicators {r s : ℕ} (c : Parts r s) (i : Fin (3*s)) :
    (if (if i ∈ c.2.val.1 then (0 : Fin 3) else if i ∈ c.2.val.2 then 2 else 1) = 1
      then 1 else 0 : ℕ) = (if i ∉ c.2.val.1 ∪ c.2.val.2 then 1 else 0) ∧
    (if (if i ∈ c.2.val.1 then (0 : Fin 3) else if i ∈ c.2.val.2 then 2 else 1) = 2
      then 1 else 0 : ℕ) = (if i ∈ c.2.val.2 then 1 else 0) := by
  have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
  by_cases hT : i ∈ c.2.val.1 <;> by_cases hU : i ∈ c.2.val.2 <;> simp_all
theorem right_indicators {r s : ℕ} (c : Parts r s) (i : Fin (3*s)) :
    (if (if i ∈ c.2.val.1 then (2 : Fin 3) else if i ∈ c.2.val.2 then 0 else 1) = 1
      then 1 else 0 : ℕ) = (if i ∉ c.2.val.1 ∪ c.2.val.2 then 1 else 0) ∧
    (if (if i ∈ c.2.val.1 then (2 : Fin 3) else if i ∈ c.2.val.2 then 0 else 1) = 2
      then 1 else 0 : ℕ) = (if i ∈ c.2.val.1 then 1 else 0) := by
  have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
  by_cases hT : i ∈ c.2.val.1 <;> by_cases hU : i ∈ c.2.val.2 <;> simp_all
theorem remaining_count {r s : ℕ} (c : Parts r s) :
    (∑ i : Fin (3*s), if i ∉ c.2.val.1 ∪ c.2.val.2 then 1 else 0 : ℕ) = s := by
  have ht := LayerCounts.mem_edgeSet.mp c.2.property
  have hf : (univ.filter fun i => i ∉ c.2.val.1 ∪ c.2.val.2) =
      (univ : Finset (Fin (3*s))) \ (c.2.val.1 ∪ c.2.val.2) := by ext; simp
  rw [← card_filter,hf,card_sdiff_of_subset (subset_univ _),card_union_of_disjoint ht.2.2]
  simp [ht.1,ht.2.1]
  omega
theorem binary_ind_one (P : Prop) [Decidable P] :
    (if (if P then (1 : Fin 3) else 0) = 1 then 1 else 0 : ℕ) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]
theorem binary_ind_two (P : Prop) [Decidable P] :
    (if (if P then (1 : Fin 3) else 0) = 2 then 1 else 0 : ℕ) = 0 := by
  by_cases h : P <;> simp [h]
theorem binary_right_one (P : Prop) [Decidable P] :
    (if (if P then (0 : Fin 3) else 1) = 1 then 1 else 0 : ℕ) = if ¬P then 1 else 0 := by
  by_cases h : P <;> simp [h]
theorem binary_right_two (P : Prop) [Decidable P] :
    (if (if P then (0 : Fin 3) else 1) = 2 then 1 else 0 : ℕ) = 0 := by
  by_cases h : P <;> simp [h]
theorem source_counts {t r s : ℕ} (c : Parts r s) :
    count (partLeft (t := t) c) 1 = r+s ∧ count (partLeft (t := t) c) 2 = s ∧
    count (partRight (t := t) c) 1 = r+s ∧ count (partRight (t := t) c) 2 = s := by
  have hc := LayerCounts.mem_vertices.mp c.1.property
  have ht := LayerCounts.mem_edgeSet.mp c.2.property
  have hb : (∑ i : Fin (2*r), if i ∉ c.1.val then 1 else 0 : ℕ) = r := by
    rw [← card_filter]
    have he : univ.filter (fun i : Fin (2*r) => i ∉ c.1.val) = univ \ c.1.val := by ext; simp
    rw [he,card_sdiff_of_subset (subset_univ _)]
    simp [hc]
    omega
  have hrem : (univ.filter (fun i : Fin (3*s) => i ∉ c.2.val.1 ∧ i ∉ c.2.val.2)).card = s := by
    simpa using remaining_count c
  have hb' : (∑ i : Fin (2*r), if i ∈ c.1.val then 0 else 1 : ℕ) = r := by
    simpa using hb
  simp only [count,Fintype.sum_sum_type]
  simp_rw [binary_ind_one,binary_ind_two,binary_right_one,binary_right_two,
    (left_indicators c _).1,(left_indicators c _).2,
    (right_indicators c _).1,(right_indicators c _).2]
  simpa [partLeft,partRight,hrem,hb',hc,ht.1,ht.2.1]
theorem parts_add {t r s : ℕ} (c : Parts r s) (i : Index t r s) :
    (partLeft c i).val+(partRight c i).val = (targetWord t r s i).val := by
  have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
  rcases i with i | i
  · rfl
  rcases i with i | i
  · by_cases h : i ∈ c.1.val <;> simp [partLeft,partRight,targetWord,h]
  · by_cases hT : i ∈ c.2.val.1 <;> by_cases hU : i ∈ c.2.val.2 <;> simp_all [partLeft,partRight,targetWord]
def canonicalEquiv (t r s : ℕ) : Fin (t+2*r+3*s) ≃ Index t r s :=
  Fintype.equivOfCardEq (by simp [Index,Fintype.card_sum]; omega)
def canonicalTarget (t r s : ℕ) : TritWord (t+2*r+3*s) := targetWord t r s ∘ canonicalEquiv t r s
def canonicalLeft {t r s : ℕ} (c : Parts r s) : TritWord (t+2*r+3*s) :=
  partLeft c ∘ canonicalEquiv t r s
def canonicalRight {t r s : ℕ} (c : Parts r s) : TritWord (t+2*r+3*s) :=
  partRight c ∘ canonicalEquiv t r s
theorem count_transfer (t r s : ℕ) (w : Index t r s → Fin 3) (d : Fin 3) :
    digitCount (w ∘ canonicalEquiv t r s) d = count w d :=
  Equiv.sum_comp (canonicalEquiv t r s) (fun i => if w i = d then 1 else 0)
theorem source_type {t r s : ℕ} (w : TritWord (t+2*r+3*s))
    (h1 : digitCount w 1 = r+s) (h2 : digitCount w 2 = s) : HasType w (alphaType t r s) := by
  have hz := count_total w
  change digitCount w 0+digitCount w 1+digitCount w 2 = Fintype.card (Fin (t+2*r+3*s)) at hz
  rw [h1,h2,Fintype.card_fin] at hz
  intro d
  fin_cases d
  · change digitCount w 0 = t+r+s
    omega
  · exact h1
  · exact h2
theorem canonicalTarget_type (t r s : ℕ) : HasType (canonicalTarget t r s) (piType t r s) := by
  intro d
  rw [canonicalTarget,count_transfer]
  simp only [count,Fintype.sum_sum_type]
  fin_cases d <;> simp [targetWord,piType]
def canonicalEdge {t r s : ℕ} (c : Parts r s) :
    LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s) := by
  classical
  have hc := source_counts (t := t) c
  refine ⟨(canonicalLeft c,canonicalRight c,canonicalTarget t r s),
    mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  refine ⟨source_type _ ?_ ?_,source_type _ ?_ ?_,canonicalTarget_type t r s, ?_⟩
  · exact (count_transfer t r s (partLeft c) 1).trans hc.1
  · exact (count_transfer t r s (partLeft c) 2).trans hc.2.1
  · exact (count_transfer t r s (partRight c) 1).trans hc.2.2.1
  · exact (count_transfer t r s (partRight c) 2).trans hc.2.2.2
  · intro i
    exact parts_add c (canonicalEquiv t r s i)
def partitionGroup (r s : ℕ) : ℕ := (2*r).choose r*((3*s).choose s*(2*s).choose s)
def partitionLoss (r s : ℕ) : ℕ := (2*r+1)*(3*s+1)*(2*s+1)
open WeightedGlobalLocalParameters
end ThreeSum.WeightedGlobalPartitionCount
end
end WeightedCache3SUMRefinement_e1ae71d


