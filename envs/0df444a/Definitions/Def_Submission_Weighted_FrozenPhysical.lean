-- Prove2me | Definitions.Def_Submission_Weighted_FrozenPhysical
-- name    : Submission_Weighted_FrozenPhysical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:00:03.469312+00:00
-- url     : https://prove2.me/theorems/608815fb-8e1d-4dd7-b0ef-aec2f6ed99bc
-- title:
--   Frozen Physical
-- statement:
--   Definitions and structural lemmas for Frozen Physical, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenPhysical.lean

import Definitions.Def_Submission_Weighted_FrozenMain
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_meets_core
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_digit
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_erase
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_lookup
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_main
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_search
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_zero
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_lt_pow_two
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_abs
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
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
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits


set_option autoImplicit false
namespace ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedFrozenQueryCost (cacheCost)
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
theorem cacheCost_le_linear {N : ℕ} (R : TritWord N) : cacheCost R≤1025*N := by
  calc
    cacheCost R≤∑ i : Fin N, 1025 := by
      unfold WeightedFrozenQueryCost.cacheCost WeightedCache.cost
      apply Finset.sum_le_sum
      intro i _
      generalize R i=d
      fin_cases d <;> norm_num [WeightedFrozenQueryCost.c]
    _=1025*N := by simp; omega
theorem meets {N pMain pLookup pSearch pDigit pZero pErase : ℕ}
    (hmain : P[pMain]?=some (body pMain pLookup pDigit pZero pErase))
    (hlookup : P[pLookup]?=some (LightTernaryQueryLookup.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (T bankCodes bankCount bankValues nearCodes nearCount nearValues powers L U : ℕ)
    (bankWords nearWords : ℕ→TritWord N) (H : TritWord N→ℤ) (Q : TritWord N) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hbankCodesSpace : bankCodes+bankCount≤lim.space)
    (hbankValuesSpace : bankValues+(N+1)*bankCount≤lim.space)
    (hnearCodesSpace : nearCodes+nearCount≤lim.space)
    (hnearValuesSpace : nearValues+nearCount≤lim.space)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((bankCount+nearCount+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcutWord : (T : ℤ)+1≤lim.word)
    (hcostWord : ((1025*N+1100 : ℕ) : ℤ)≤lim.word)
    (hvalueWord : 4*((4^N : ℕ) : ℤ)*(U : ℤ)+3≤lim.word)
    (hpowers : Powers μ powers (2*N)) (hL : L≤2*N)
    (hbankSmall : bankCount<2^L) (hnearSmall : nearCount<2^L)
    (hH : ∀ R, |H R|≤(U : ℤ))
    (hbankRead : ∀ j<bankCount, μ (bankCodes+j)=(address (bankWords j) : ℤ))
    (hbankSorted : ∀ i j, i<j → j<bankCount → address (bankWords i)<address (bankWords j))
    (hbankPresent : ∀ R : TritWord N, cacheCost R≤T → ∃ j<bankCount, bankWords j=R)
    (hbankValues : ∀ K≤N, ∀ j<bankCount, μ (bankValues+K*bankCount+j)=stageValue K H (bankWords j))
    (hnearRead : ∀ j<nearCount, μ (nearCodes+j)=(address (nearWords j) : ℤ))
    (hnearSorted : ∀ i j, i<j → j<nearCount → address (nearWords i)<address (nearWords j))
    (hnearPresent : ∀ R : TritWord N, Below R Q → T<cacheCost R → ∃ j<nearCount, nearWords j=R)
    (hnearValues : ∀ j<nearCount, μ (nearValues+j)=H (nearWords j)) :
    ∀ K≤N, ∀ R : TritWord N, Below R Q → ∀ d, d+K+2*N+L+3≤lim.depth →
      Meets lim P pMain d
        (inputs N K (cacheCost R) T (address R) bankCodes bankCount bankValues
          nearCodes nearCount nearValues powers L) μ (queryTime L T K R)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ) := by
  have hcast {a b : ℕ} (h : a≤b) : (a : ℤ)≤(b : ℤ) := by exact_mod_cast h
  have hwordPow : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word :=
    (hcast (show 2^(2*N+1)≤bankCount+nearCount+2^(2*N+1)+16 by omega)).trans hword
  have hwordBank : ((bankCount+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word := by
    have hle : bankCount+2^(2*N+1)+16≤bankCount+nearCount+2^(2*N+1)+16 := by omega
    exact (hcast hle).trans hword
  have hwordNear : ((nearCount+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word := by
    have hle : nearCount+2^(2*N+1)+16≤bankCount+nearCount+2^(2*N+1)+16 := by omega
    exact (hcast hle).trans hword
  have hBnonneg : 0≤((4^N : ℕ) : ℤ)*(U : ℤ) := by positivity
  have hBword : ((4^N : ℕ) : ℤ)*(U : ℤ)≤lim.word := by nlinarith
  have hUword : ((4^N*U : ℕ) : ℤ)≤lim.word := by simpa [Nat.cast_mul] using hBword
  have hbound (K : ℕ) (hKN : K≤N) (R : TritWord N) :
      |stageValue K H R|≤((4^N*U : ℕ) : ℤ) := by
    have hs := stageValue_abs K hKN H U hH R
    have hp : ((4^K : ℕ) : ℤ)≤((4^N : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤4) hKN
    simpa [Nat.cast_mul] using hs.trans (mul_le_mul_of_nonneg_right hp (by positivity))
  have hHbound (R : TritWord N) : |H R|≤((4^N*U : ℕ) : ℤ) := by
    simpa using hbound 0 (by omega) R
  have hargs : ∀ K≤N, ∀ R : TritWord N,
      ∀ x∈inputs N K (cacheCost R) T (address R) bankCodes bankCount bankValues
        nearCodes nearCount nearValues powers L, |x|≤lim.word := by
    intro K hKN R x hx
    have hrank := cacheCost_le_linear R
    have haddress := address_lt_pow_two R
    have haddressWord : (address R : ℤ)≤lim.word := by
      have hpow : 2^(2*N)≤2^(2*N+1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hle : address R≤2^(2*N+1) := (Nat.le_of_lt haddress).trans hpow
      exact (hcast hle).trans hwordPow
    have hbc : (bankCodes : ℤ)≤lim.word := (hcast (show bankCodes≤lim.space by omega)).trans hw
    have hbn : (bankCount : ℤ)≤lim.word := (hcast (show bankCount≤lim.space by omega)).trans hw
    have hbv : (bankValues : ℤ)≤lim.word := (hcast (show bankValues≤lim.space by omega)).trans hw
    have hnc : (nearCodes : ℤ)≤lim.word := (hcast (show nearCodes≤lim.space by omega)).trans hw
    have hnn : (nearCount : ℤ)≤lim.word := (hcast (show nearCount≤lim.space by omega)).trans hw
    have hnv : (nearValues : ℤ)≤lim.word := (hcast (show nearValues≤lim.space by omega)).trans hw
    have hp : (powers : ℤ)≤lim.word := (hcast (show powers≤lim.space by omega)).trans hw
    simp only [inputs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals rw [abs_of_nonneg (by positivity)]; omega
  have hbankLeaf : ∀ K≤N, ∀ R : TritWord N, Below R Q → cacheCost R≤T →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [bankCodes,bankCount,address R,bankValues,powers,L,K] μ
        (LightTernaryQueryLookup.time L) (fun v μ' => v=stageValue K H R ∧ μ'=μ) := by
    intro K hKN R _ hr d hd
    obtain ⟨j,hj,heq⟩ := hbankPresent R hr
    have hvaluesSpace : bankValues+(K+1)*bankCount≤lim.space :=
      (Nat.add_le_add_left (Nat.mul_le_mul_right bankCount (by omega)) bankValues).trans hbankValuesSpace
    have hv : μ (bankValues+K*bankCount+j)=stageValue K H R := by rw [hbankValues K hKN j hj,heq]
    have hs : ∀ i j, i<j → j<bankCount →
        (address (bankWords i) : ℤ)<(address (bankWords j) : ℤ) := by
      intro i j hij hj
      exact_mod_cast hbankSorted i j hij hj
    have hc := LightTernaryQueryLookup.meets hlookup hsearch μ (fun j => (address (bankWords j) : ℤ))
      (stageValue K H R) hw hbankCodesSpace hvaluesSpace hspace hwordBank hbankRead hpowers hs hj
      hv (hbound K hKN R) hUword hL hbankSmall hd
    simpa only [heq,Nat.cast_zero] using hc
  have hnearLeaf : ∀ R : TritWord N, Below R Q → T<cacheCost R →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [nearCodes,nearCount,address R,nearValues,powers,L,0] μ
        (LightTernaryQueryLookup.time L) (fun v μ' => v=H R ∧ μ'=μ) := by
    intro R hRQ hr d hd
    obtain ⟨j,hj,heq⟩ := hnearPresent R hRQ hr
    have hv : μ (nearValues+0*nearCount+j)=H R := by simp [hnearValues j hj,heq]
    have hs : ∀ i j, i<j → j<nearCount →
        (address (nearWords i) : ℤ)<(address (nearWords j) : ℤ) := by
      intro i j hij hj
      exact_mod_cast hnearSorted i j hij hj
    have hc := LightTernaryQueryLookup.meets (stage := 0) hlookup hsearch μ
      (fun j => (address (nearWords j) : ℤ)) (H R) hw hnearCodesSpace
      (by simpa using hnearValuesSpace) hspace hwordNear hnearRead hpowers hs hj hv
      (hHbound R) hUword hL hnearSmall hd
    simpa only [heq,Nat.cast_zero] using hc
  exact meets_core hmain hdigit hzero herase T bankCodes bankCount bankValues nearCodes nearCount nearValues
    powers L U H Q μ hw hspace hwordPow hNword hcutWord hvalueWord hpowers hH hargs hbankLeaf hnearLeaf
def program_meets {N : ℕ} :=
  meets (N := N) (lim := lim) (P := program) program_main program_lookup program_search
    program_digit program_zero program_erase
end ThreeSum.LightWeightedFrozenQuery


