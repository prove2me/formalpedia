-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRows
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:07:39.298709+00:00
-- url     : https://prove2.me/theorems/c9f37fdb-6be0-4213-b9fe-407db9fb621a
-- title:
--   WantedRows
-- statement:
--   Definitions and structural lemmas for WantedRows, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedRows.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRowDispatch
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedState
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_program_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_code_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedState_Snapshot_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedState_Snapshot_result_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedState_Snapshot_transfer
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedRowDispatch_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_code_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
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
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedWantedRows
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 7000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
def roundBody (pRow : ℕ) : Stmt :=
  .call pRow
    [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20,
      v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33, v 34, v 35, v 36, v 37, v 38,
      (_root_.Light.Expr.op _root_.Light.Op.add) (v 39) ((_root_.Light.Expr.op _root_.Light.Op.mul) (k 3) (v 48)),
      (_root_.Light.Expr.op _root_.Light.Op.add) (v 47) (v 48), v 41, v 42, v 43, v 44, v 45]
    49
def body (pRow : ℕ) : Stmt :=
  .for 48 (v 46) (roundBody pRow)
def args {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (out bankValues caps records count dst fbase gbase hbase stride tail : ℕ) : List ℤ :=
  LightWeightedWantedRowDispatch.args f g Qstar out bankValues caps records dst fbase gbase hbase stride tail ++
    [(count : ℤ), dst]
def time (count t : ℕ) : ℕ :=
  count * (LightWeightedWantedRowDispatch.time t + 200) + 100
def score {N : ℕ} (F G : ℕ → TritWord N → ℤ) (group : ℕ → ℕ) (Q : ℕ → TritWord N) (j : ℕ) : ℤ :=
  stageValue N (LightWeightedWantedQuery.H (F (group j)) (G (group j))) (Q j)
def Inv {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (out bankValues caps records count dst fbase gbase hbase stride tail : ℕ) (μ : ℕ → ℤ) (value : ℕ → ℤ) (j : ℕ)
    (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ =
        ⟨frame (args f g Qstar out bankValues caps records count dst fbase gbase hbase stride tail ++ [(j : ℤ), r]),
          ν⟩ ∧
      Kept μ ν dst ∧ ∀ k < j, ν (dst + k) = value k
theorem meets {e : LightWeightedPreparedWanted.Entries}
    {pMain pRow pPrepare N out bankValues caps records count dst fbase gbase hbase stride tail groups d t : ℕ}
    (hmain : P[pMain]? = some (body pRow)) (hrow : P[pRow]? = some (LightWeightedWantedRowDispatch.body pPrepare))
    (hprepare : P[pPrepare]? = some (LightWeightedPreparedWanted.body e))
    (lib : LightWeightedPreparedWanted.Library P e) (f g : Config) (Qstar : TritWord N) (Q : ℕ → TritWord N)
    (group : ℕ → ℕ) (F G : ℕ → TritWord N → ℤ) (E : Enumeration N f.T f.nb) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hrecords : records + 3 * count ≤ dst) (hdst : dst + count ≤ f.a)
    (hspace : f.a ≤ lim.space) (hcodesBefore : f.bank + f.nb ≤ dst) (hfg : fbase + groups * stride ≤ gbase)
    (hgh : gbase + groups * stride ≤ hbase) (hHdst : hbase + groups * stride ≤ dst) (htail : tail + f.nb = stride)
    (hstage : stride = (N + 1) * f.nb) (hreadGroup : ∀ j < count, μ (records + 3 * j + 2) = (group j : ℤ))
    (hreadQ : ∀ j < count, μ (records + 3 * j + 1) = (address (Q j) : ℤ)) (hgroup : ∀ j < count, group j < groups)
    (hRank : ∀ j < count, cacheCost (Q j) = cacheCost Qstar) (hgroupsWord : (groups : ℤ) ≤ lim.word)
    (hcountWord : (count : ℤ) + 1 ≤ lim.word) (hstrideWord : (stride : ℤ) ≤ lim.word)
    (htailWord : (tail : ℤ) ≤ lim.word)
    (hsnapshot :
      ∀ j < count,
        Snapshot lim out (hbase + group j * stride) caps (sourceConfig f fbase stride tail (group j))
          (sourceConfig g gbase stride tail (group j)) μ (Q j) E (F (group j)) (G (group j)))
    (htime :
      ∀ j < count,
        LightWeightedPreparedWanted.time (sourceConfig f fbase stride tail (group j))
            (sourceConfig g gbase stride tail (group j)) (Q j) ≤
          t)
    (hd : d + 3 * N + f.L + 15 ≤ lim.depth) :
    Meets lim P pMain d (args f g Qstar out bankValues caps records count dst fbase gbase hbase stride tail) μ
      (time count t) (fun _ ν => Kept μ ν dst ∧ ∀ j < count, ν (dst + j) = score F G group Q j) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv f g Qstar out bankValues caps records count dst fbase gbase hbase stride tail μ (score F G group Q))
      count (LightWeightedWantedRowDispatch.time t + 180) ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ, ?_, ?_, ?_⟩
    · simp only [update_frame_setLocal]
      congr 1
      simp only [args, LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args,
        LightWeightedWantedQuery.args, LightWeightedNearPair.args, setLocal]
      exact (frame_append_zeros _ 1).symm
    · intro x _; rfl
    · intro k hk; omega
  case round =>
    rintro j _ hj _ ⟨r, ν, rfl, hkeep, hvalues⟩
    have hg := hgroup j hj
    have hnext : group j * stride + stride ≤ groups * stride :=
      by
      have h := Nat.mul_le_mul_right stride (show group j + 1 ≤ groups by omega)
      simpa only [Nat.add_mul, Nat.one_mul] using h
    have hFbefore : fbase + group j * stride + tail + f.nb ≤ dst := by omega
    have hGbefore : gbase + group j * stride + tail + f.nb ≤ dst := by omega
    have hHbefore : hbase + group j * stride + (N + 1) * f.nb ≤ dst :=
      by
      rw [← hstage]
      omega
    have S := (hsnapshot j hj).transfer hkeep hcodesBefore hFbefore hGbefore hHbefore
    have hquery := (S.meets hprepare lib (d := d + 2) (by dsimp [sourceConfig]; omega)).mono_time (htime j hj)
    have hrG : ν ((records + 3 * j) + 2) = (group j : ℤ) := by rw [hkeep _ (by omega)]; exact hreadGroup j hj
    have hrQ : ν ((records + 3 * j) + 1) = (address (Q j) : ℤ) := by rw [hkeep _ (by omega)]; exact hreadQ j hj
    have hD : LightWeightedPreparedWanted.D (Q j) f.T = LightWeightedPreparedWanted.D Qstar f.T :=
      by
      unfold LightWeightedPreparedWanted.D
      rw [hRank j hj]
    have hqNat : address (Q j) ≤ 4 ^ (N + 1) :=
      by
      have hlt : address (Q j) < 4 ^ N := by
        simpa only [address, TernaryBankEnumeration.wordList_length] using
          TernaryAddresses.code_lt (TernaryBankEnumeration.wordList (Q j))
            (TernaryBankEnumeration.wordList_digits (Q j))
      exact (Nat.le_of_lt hlt).trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hQWord : (address (Q j) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hqNat).trans (hsnapshot j hj).setupWord
    have hmulWord : (group j : ℤ) * (stride : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show group j * stride ≤ lim.space by omega) :
            (group j : ℤ) * (stride : ℤ) ≤ (lim.space : ℤ)).trans
        hw
    have hfWord : (fbase : ℤ) + (group j : ℤ) * (stride : ℤ) + (tail : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show fbase + group j * stride + tail ≤ lim.space by omega) :
            (fbase : ℤ) + (group j : ℤ) * (stride : ℤ) + (tail : ℤ) ≤ (lim.space : ℤ)).trans
        hw
    have hgWord : (gbase : ℤ) + (group j : ℤ) * (stride : ℤ) + (tail : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show gbase + group j * stride + tail ≤ lim.space by omega) :
            (gbase : ℤ) + (group j : ℤ) * (stride : ℤ) + (tail : ℤ) ≤ (lim.space : ℤ)).trans
        hw
    have hhWord : (hbase : ℤ) + (group j : ℤ) * (stride : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show hbase + group j * stride ≤ lim.space by omega) :
            (hbase : ℤ) + (group j : ℤ) * (stride : ℤ) ≤ (lim.space : ℤ)).trans
        hw
    have hgWord' : (group j : ℤ) ≤ lim.word :=
      by
      have hz : (group j : ℤ) < (groups : ℤ) := by exact_mod_cast hg
      omega
    have hc :=
      LightWeightedWantedRowDispatch.meets (d := d + 1) (record := records + 3 * j) (dst := dst + j) (bankValues :=
        bankValues) hrow f g Qstar (Q j) ν (score F G group Q j) hw (by omega) (by omega) hrG hrQ hgWord' hQWord
        hstrideWord htailWord hmulWord hfWord hgWord hhWord hD (S.result_bound) (by omega) hquery
    have htrip : (3 : ℤ) * (j : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show 3 * j ≤ lim.space by omega) : (3 : ℤ) * (j : ℤ) ≤ (lim.space : ℤ)).trans hw
    have hrecordWord : (records : ℤ) + 3 * (j : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show records + 3 * j ≤ lim.space by omega) :
            (records : ℤ) + 3 * (j : ℤ) ≤ (lim.space : ℤ)).trans
        hw
    have hdstWord : (dst : ℤ) + (j : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show dst + j ≤ lim.space by omega) : (dst : ℤ) + (j : ℤ) ≤ (lim.space : ℤ)).trans hw
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      first
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args,
              LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args,
              LightWeightedNearPair.args, LightWeightedWantedRowDispatch.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [args, LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args,
                LightWeightedWantedQuery.args, LightWeightedNearPair.args, LightWeightedWantedRowDispatch.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, LightWeightedWantedRowDispatch.args,
              LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args, LightWeightedNearPair.args,
              LightWeightedWantedRowDispatch.time] <;> omega)
      on_goal -1 => (rintro result ξ ⟨ν', hkeep', rfl⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine
      ⟨by
        simp [args, LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args,
          LightWeightedWantedQuery.args, LightWeightedNearPair.args, setLocal],
        result, Function.update ν' (dst + j) (score F G group Q j), ?_, ?_, ?_⟩
    ·
      simp [Inv, update_frame_setLocal, args, LightWeightedWantedRowDispatch.args, LightWeightedPreparedWanted.args,
        LightWeightedWantedQuery.args, LightWeightedNearPair.args]
    · intro x hx
      rw [Function.update_of_ne (by omega), hkeep' x (by omega)]
      exact hkeep x hx
    · intro k hk
      by_cases he : k = j
      · subst k; simp
      · have hkj : k < j := by omega
        rw [Function.update_of_ne (by omega), hkeep' _ (by omega)]
        exact hvalues k hkj
  case done =>
    rintro _ _ ⟨r, ν, rfl, hkeep, hvalues⟩
    exact ⟨hkeep, hvalues⟩
  case bound =>
    rintro j _ hj _ ⟨r, ν, rfl, hkeep, hvalues⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, LightWeightedWantedRowDispatch.args,
          LightWeightedPreparedWanted.args, LightWeightedWantedQuery.args, LightWeightedNearPair.args] <;> omega)
def program : Program :=
  LightWeightedPreparedWanted.program ++ [LightWeightedWantedRowDispatch.body 40, body 41]
theorem program_library : LightWeightedPreparedWanted.Library program LightWeightedPreparedWanted.entries :=
  by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, rfl, rfl, rfl⟩
  constructor <;> rfl
def program_meets {N out bankValues caps records count dst fbase gbase hbase stride tail groups d t : ℕ} :=
  meets (lim := lim) (P := program) (pMain := 42) (pRow := 41) (pPrepare := 40) (N := N) (out := out) (bankValues :=
    bankValues) (caps := caps) (records := records) (count := count) (dst := dst) (fbase := fbase) (gbase := gbase)
    (hbase := hbase) (stride := stride) (tail := tail) (groups := groups) (d := d) (t := t) rfl rfl rfl program_library
end ThreeSum.LightWeightedWantedRows
end
end WeightedCache3SUMRefinement_e1ae71d


