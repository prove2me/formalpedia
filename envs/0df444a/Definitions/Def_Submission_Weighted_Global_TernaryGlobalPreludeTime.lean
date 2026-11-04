-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeTime
-- name    : Submission_Weighted_Global_TernaryGlobalPreludeTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:29:25.285206+00:00
-- url     : https://prove2.me/theorems/20c10e4d-0342-4772-ada3-3bb850d96d75
-- title:
--   Ternary Global Prelude Time
-- statement:
--   Definitions and structural lemmas for Ternary Global Prelude Time, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeTime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeResources
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetupBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsTime
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightCacheEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightExtensionBackend_time_polynomial
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_time_polynomial
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightPairSearch_time_bound
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightScales_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_time_bound
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_time_bound
import Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_time_linear_parameters
import Theorems.Thm_ThreeSum_LightWeightedGlobalExtensionBackendSetup_time_polynomial
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_backendLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_dimensionsLibrary_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearSource_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
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
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_log2_le_of_le_pow
import Theorems.Thm_ThreeSum_WeightedGlobalGlobalPreludeResources_need_meets
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
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.backendLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.dimensionsLibrary_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.program_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
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
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalGlobalPreludeTime
open Light LightWeightedGlobalGlobalPrelude LightExtensionBackendLayout
open Filter WeightedGlobalCoverScale
set_option maxHeartbeats 4000000
def uniformTime (M b p K κ n : ℕ) : ℕ :=
  (20000000000+1000+500*(Nat.size M+1)+LightNatPower.time κ+LightNatPower.time 6+5000)*
    (LightExtensionBackendLayout.params (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ)))^10
theorem bits_bound {M : ℕ} (hM : 1<M) (n : ℕ) :
    Scales.inputBits n≤Nat.size M*LightWeightedGlobalDimensions.r M n :=by
  have hn : n≤n^2 :=Nat.le_self_pow (by decide) n
  have hc : n^2≤M^(LightWeightedGlobalDimensions.r M n) :=Nat.le_pow_clog hM _
  have hm : M≤2^(Nat.size M) :=(Nat.lt_size_self M).le
  have hp:=Nat.pow_le_pow_left hm (LightWeightedGlobalDimensions.r M n)
  have ht : n≤2^(Nat.size M*LightWeightedGlobalDimensions.r M n) :=by
    simpa only [←pow_mul] using hn.trans (hc.trans hp)
  exact log2_le_of_le_pow ht
theorem time_le_uniform {M b p K κ : ℕ} [Fact p.Prime] (hM : 1<M) (n free : ℕ) :
    LightWeightedGlobalGlobalPreludeProof.time M b p K κ n free≤uniformTime M b p K κ n :=by
  let J:=LightWeightedGlobalDimensions.J M b n (n^κ)
  let D:=LightWeightedGlobalDimensions.dim M b p K n (n^κ)
  let Q:=p^D
  let B:=LightExtensionBackendLayout.params D p Q J
  have hB : 1≤B :=by dsimp [B,LightExtensionBackendLayout.params]; omega
  have hp : 1≤p :=(Fact.out : p.Prime).pos
  have hr : LightWeightedGlobalDimensions.r M n≤J :=by dsimp [J,LightWeightedGlobalDimensions.J,WeightedGlobalSignedPadding.paddedLength]; omega
  have hJ : J+1≤B :=by dsimp [B,LightExtensionBackendLayout.params]; omega
  have hs:=LightScales.time_bound n
  have hb:=bits_bound hM n
  have hs' : LightScales.time n≤500*(Nat.size M+1)*B :=by
    have hh:=Nat.mul_le_mul_left (Nat.size M) hr
    nlinarith
  have hd:=LightWeightedGlobalDimensions.time_linear_parameters M b p K n (n^κ)
  have hd' : LightWeightedGlobalDimensions.time M b p K n (n^κ)≤1000*B :=by
    change LightWeightedGlobalDimensions.time M b p K n (n^κ)≤_
    apply hd.trans
    apply Nat.mul_le_mul_left
    dsimp [B,LightExtensionBackendLayout.params,J,D,Q]
    omega
  have hbackend:=LightWeightedGlobalExtensionBackendSetup.time_polynomial (backend free) D p Q J
  have h10 : B≤B^10 :=by simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1≤10 by decide)
  have h10pos : 1≤B^10 :=Nat.one_le_pow _ _ hB
  have hsb:=hs'.trans (Nat.mul_le_mul_left (500*(Nat.size M+1)) h10)
  have hdb:=hd'.trans (Nat.mul_le_mul_left 1000 h10)
  change _≤_ at hbackend
  change LightNatPower.time κ+LightScales.time n+LightWeightedGlobalDimensions.time M b p K n (n^κ)+
    LightWeightedGlobalExtensionBackendSetup.time (backend free) D p Q J+LightNatPower.time 6+5000≤
    (20000000000+1000+500*(Nat.size M+1)+LightNatPower.time κ+LightNatPower.time 6+5000)*B^10
  change LightWeightedGlobalExtensionBackendSetup.time (backend free) D p Q J≤20000000000*B^10 at hbackend
  nlinarith
def need_meets_uniform {lim : Limits} {M b p K κ n U free depth : ℕ} [Fact p.Prime]
    (μ : ℕ→ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (H : (WeightedGlobalGlobalPreludeResources.need M b p K κ n U).Ok lim free depth) :=
  (WeightedGlobalGlobalPreludeResources.need_meets μ hM hb hn H).mono
    (time_le_uniform hM n free) (fun _ _ h=>h)
end ThreeSum.WeightedGlobalGlobalPreludeTime


