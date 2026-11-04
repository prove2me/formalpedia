-- Prove2me | Definitions.Def_Submission_Weighted_BankCanonical
-- name    : Submission_Weighted_BankCanonical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:54:15.611716+00:00
-- url     : https://prove2.me/theorems/263da532-4778-478b-a782-d8071ea86b1f
-- title:
--   Bank Canonical
-- statement:
--   Definitions and structural lemmas for Bank Canonical, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCanonical.lean

import Definitions.Def_Submission_Weighted_BankStageModel
import Definitions.Def_Submission_Weighted_BankEnumeration
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_fromList
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_injective
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_mem_words
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_fromList
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_injective
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_mem_words
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits


set_option autoImplicit false
namespace ThreeSum.WeightedBankCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedBankEnumeration ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
def word (N T j : ℕ) : TritWord N :=
  if hj : j<(words N T).length then
    fromList (words N T)[j] ((mem_words N T _).mp (List.getElem_mem hj)).1
      ((mem_words N T _).mp (List.getElem_mem hj)).2.1
  else fun _ => 0
theorem wordList_word {N T j : ℕ} (hj : j<(words N T).length) :
    wordList (word N T j)=(words N T)[j] := by
  unfold word
  rw [dif_pos hj]
  exact wordList_fromList _ _ _
theorem word_rank {N T j : ℕ} (hj : j<(words N T).length) : cacheCost (word N T j)≤T := by
  have hr := ((mem_words N T _).mp (List.getElem_mem hj)).2.2
  rwa [← wordList_word hj,wordList_cost] at hr
def enumeration (N T : ℕ) : Enumeration N T (codes N T).length where
  word := word N T
  mem := fun j hj => word_rank (by simpa only [codes_length] using hj)
  complete := by
    intro R hR
    have hm : wordList R∈words N T := (wordList_mem_words R).mpr (mem_bank.mpr hR)
    obtain ⟨j,hj,heq⟩ := List.mem_iff_getElem.mp hm
    refine ⟨j,by simpa only [codes_length] using hj,?_⟩
    exact wordList_injective N ((wordList_word hj).trans heq)
end ThreeSum.WeightedBankCanonical


