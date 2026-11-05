-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:57:34.162582+00:00
-- url     : https://prove2.me/theorems/f67b1917-eb0a-4f60-99e6-1177198975fb
-- title:
--   PreparedWanted
-- statement:
--   Definitions and structural lemmas for PreparedWanted, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedWanted.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryPlan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearCanonical
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
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
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_program_main
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
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedQueryPlan_Resources_costWord
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedQueryPlan_ready
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankCanonical_read_of_seg
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankCanonical_sorted
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_outside_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_outside_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_read_of_seg
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_sorted
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
namespace ThreeSum.LightWeightedPreparedWanted
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}
structure Entries where
  wanted : LightWeightedWantedQuery.Entries
  wantedMain : ℕ
  setup : ℕ
  powers : ℕ
  digits : ℕ
  enum : ℕ
  branch : ℕ
structure Library (P : Program) (e : Entries) : Prop where
  wanted : LightWeightedWantedQuery.Library P e.wanted
  wantedMain : P[e.wantedMain]? = some (LightWeightedWantedQuery.body e.wanted)
  setup : P[e.setup]? = some (LightWeightedNearSetup.body e.powers e.digits e.enum)
  powers : P[e.powers]? = some powTableBody
  digits : P[e.digits]? = some (LightWeightedNearDigits.body e.wanted.near.digit)
  enum : P[e.enum]? = some (LightWeightedNearEnumeration.body e.branch)
  branch : P[e.branch]? = some (LightWeightedNearEnumeration.branchBody e.enum)
def body (e : Entries) : Stmt :=
  _root_.Light.Stmt.seq (.call e.setup [v 0, v 37, v 35, v 1, v 3, v 38, v 9] 39)
    (_root_.Light.Stmt.seq (.set 2 (v 39))
      (_root_.Light.Stmt.seq (.set 19 (v 39))
        (.call e.wantedMain
          [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19,
            v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33, v 34, v 35, v 36]
          0)))
def D {N : ℕ} (Q : TritWord N) (T : ℕ) : ℕ :=
  cacheCost Q - (T + 1)
def rows {N : ℕ} (Q : TritWord N) (T : ℕ) : ℕ :=
  (WeightedNearEnumeration.codes (WeightedBankEnumeration.wordList Q) (D Q T)).length
def args {N : ℕ} (out bankValues caps : ℕ) (f g : Config) (Q : TritWord N) : List ℤ :=
  LightWeightedWantedQuery.args 0 out bankValues f g Q ++ [(D Q f.T : ℤ), (caps : ℤ)]
def time {N : ℕ} (f g : Config) (Q : TritWord N) : ℕ :=
  LightWeightedNearSetup.time Q (D Q f.T) + LightWeightedWantedQuery.time (rows Q f.T) f g Q + 400
theorem meets {e : Entries} {pMain N out bankValues caps d : ℕ} (hmain : P[pMain]? = some (body e)) (lib : Library P e)
    (f g : Config) (μ : ℕ → ℤ) (Q : TritWord N) (E : Enumeration N f.T f.nb) (F G : TritWord N → ℤ)
    (Rf : Resources lim (rows Q f.T) f F) (Rg : Resources lim (rows Q f.T) g G) (hQ : f.T < cacheCost Q)
    (hga : g.a = f.a) (hgp : g.powers = f.powers) (hgactive : g.activeBase = f.activeBase) (hgbank : g.bank = f.bank)
    (hgnb : g.nb = f.nb) (hgT : g.T = f.T) (hbankRead : ∀ j < f.nb, μ (f.bank + j) = (address (E.word j) : ℤ))
    (hbankSorted : ∀ j k, j < k → k < f.nb → address (E.word j) < address (E.word k))
    (hFbank : ∀ j < f.nb, μ (f.bv + j) = binomialZeta F (E.word j))
    (hGbank : ∀ j < f.nb, μ (g.bv + j) = binomialZeta G (E.word j)) (hbankBefore : f.bank + f.nb ≤ f.a)
    (hFbefore : f.bv + f.nb ≤ f.a) (hGbefore : g.bv + f.nb ≤ f.a) (hHbefore : bankValues + (N + 1) * f.nb ≤ f.a)
    (hHbank : LightWeightedBankSweep.Stages E (fun k => stageValue k (LightWeightedWantedQuery.H F G)) bankValues N μ)
    (hdst : f.a + rows Q f.T ≤ caps) (hcaps : caps + N ≤ f.activeBase) (hactive : f.activeBase + N ≤ f.powers)
    (hsetupWord : ((4 ^ (N + 1) : ℕ) : ℤ) ≤ lim.word) (hGRead : ReadBefore N (rows Q f.T) g f.ws)
    (hFbeforeG : f.vals + rows Q f.T ≤ g.ws) (hFout : f.vals + rows Q f.T ≤ out) (hGout : g.vals + rows Q f.T ≤ out)
    (hOutSpace : out + rows Q f.T ≤ lim.space) (hOutKeep : f.ws ≤ out) (hproductWord : (f.U : ℤ) * (g.U : ℤ) ≤ lim.word)
    (hqueryWord : 4 * ((4 ^ N : ℕ) : ℤ) * ((f.U * g.U : ℕ) : ℤ) + 3 ≤ lim.word)
    (hd : d + 3 * N + f.L + 13 ≤ lim.depth) :
    Meets lim P pMain d (args out bankValues caps f g Q) μ (time f g Q)
      (fun v ν => v = stageValue N (LightWeightedWantedQuery.H F G) Q ∧ Kept μ ν f.a) :=
  by
  have hw := Rf.hw
  have hws : f.ws ≤ lim.space := by
    have := Rf.hmetadataRanks; have := Rf.hrankVals; have := Rf.hvals; have := Rf.hfr
    omega
  have hD : D Q f.T ≤ 2740 * N := (Nat.sub_le _ _).trans (LightWeightedFrozenQuery.cacheCost_le_linear Q)
  have hsetup :=
    LightWeightedNearSetup.meets (d := d + 1) lib.setup lib.powers lib.digits lib.wanted.near.digit
      lib.wanted.near.erase lib.enum lib.branch μ Q hw (Rf.hp.trans hws) hsetupWord Rf.costWord hD hdst hcaps hactive
      (by omega)
  apply Meets.of_body hmain
  unfold body args time
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
    | refine _root_.Light.Ends.callToThen (hsetup _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsetup ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, rows, D, LightWeightedNearSetup.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedWantedQuery.args, LightWeightedNearPair.args, rows, D, LightWeightedNearSetup.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, rows, D, LightWeightedNearSetup.time] <;> omega)
    on_goal -1 =>
      (rintro count ν ⟨hcount, hNear, hPowers, hActive, hkeep⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcount' : count = (rows Q f.T : ℤ) := hcount
  have hrowsWord : (rows Q f.T : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show rows Q f.T ≤ lim.space by have := Rf.ha; omega)).trans hw
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (rows Q f.T) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount', LightWeightedWantedQuery.args,
            LightWeightedNearPair.args]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcount', LightWeightedWantedQuery.args, LightWeightedNearPair.args] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount', LightWeightedWantedQuery.args,
            LightWeightedNearPair.args] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (rows Q f.T) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount', LightWeightedWantedQuery.args,
            LightWeightedNearPair.args]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcount', LightWeightedWantedQuery.args, LightWeightedNearPair.args] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount', LightWeightedWantedQuery.args,
            LightWeightedNearPair.args] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  let nearWords := WeightedNearCanonical.word Q (D Q f.T)
  have hnearRead : ∀ j < rows Q f.T, ν (f.a + j) = (address (nearWords j) : ℤ) :=
    WeightedNearCanonical.read_of_seg Q ν hNear
  have hbankRead' : ∀ j < f.nb, ν (f.bank + j) = (address (E.word j) : ℤ) :=
    by
    intro j hj
    rw [hkeep _ (by omega)]
    exact hbankRead j hj
  have hFbank' : ∀ j < f.nb, ν (f.bv + j) = binomialZeta F (E.word j) :=
    by
    intro j hj
    rw [hkeep _ (by omega)]
    exact hFbank j hj
  have hGbank' : ∀ j < g.nb, ν (g.bv + j) = binomialZeta G (E.word j) :=
    by
    intro j hj
    rw [hkeep _ (by omega)]
    exact hGbank j (by omega)
  have hnearSorted : ∀ j k, j < k → k < rows Q f.T → address (nearWords j) < address (nearWords k) :=
    WeightedNearCanonical.sorted Q (D Q f.T)
  have hnearPresent : ∀ W, Below W Q → f.T < cacheCost W → ∃ j < rows Q f.T, nearWords j = W := fun W hW hR =>
    WeightedNearCanonical.outside_complete Q W hQ hW hR
  have hnearRows : ∀ j < rows Q f.T, Below (nearWords j) Q ∧ f.T < cacheCost (nearWords j) := fun j hj =>
    WeightedNearCanonical.outside_rows Q hQ hj
  have Rf' : Ready lim (rows Q f.T) f ν Q E.word nearWords F :=
    ready Rf hnearRead hbankRead' hActive hPowers hFbank' hbankSorted hnearSorted E.complete hnearPresent hnearRows
  have Rg' : Ready lim (rows Q f.T) g ν Q E.word nearWords G :=
    by
    apply ready Rg
    · simpa only [hga] using hnearRead
    · simpa only [hgbank, hgnb] using hbankRead'
    · simpa only [hgactive] using hActive
    · simpa only [hgp] using hPowers
    · exact hGbank'
    · simpa only [hgnb] using hbankSorted
    · exact hnearSorted
    · simpa only [hgT, hgnb, WeightedBankEnumeration.cacheCost] using E.complete
    · simpa only [hgT] using hnearPresent
    · simpa only [hgT] using hnearRows
  have hHbank' :
    LightWeightedBankSweep.Stages E (fun k => stageValue k (LightWeightedWantedQuery.H F G)) bankValues N ν :=
    by
    intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb hk
    have hs : (N + 1) * f.nb = N * f.nb + f.nb := by ring
    rw [hkeep _ (by omega)]
    exact hHbank k hk j hj
  have hWanted :=
    LightWeightedWantedQuery.meets (d := d + 1) lib.wantedMain lib.wanted f g ν Q E nearWords F G Rf' Rg' hGRead
      hFbeforeG hFout hGout hOutSpace hOutKeep (by have := Rf.ha; omega) hHbank' hproductWord hqueryWord (by omega)
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
    | refine _root_.Light.Ends.callToThen (hWanted _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hWanted ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, LightWeightedNearSetup.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedWantedQuery.args, LightWeightedNearPair.args, LightWeightedNearSetup.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedWantedQuery.args,
            LightWeightedNearPair.args, LightWeightedNearSetup.time] <;> omega)
    on_goal -1 => (rintro result ξ ⟨hout, hkeepWanted⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hout, ?_⟩
  intro x hx
  exact (hkeepWanted x (by have := Rf.ha; omega)).trans (hkeep x hx)
def entries : Entries :=
  ⟨LightWeightedWantedQuery.entries, 39, 37, 30, 36, 31, 32⟩
def program : Program :=
  LightWeightedWantedQuery.program ++ [body entries]
theorem program_library : Library program entries :=
  by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, rfl, rfl, rfl⟩
  constructor <;> rfl
@[simp]
theorem program_main : program[40]? = some (body entries) :=
  rfl
def program_meets {N out bankValues caps d : ℕ} :=
  meets (lim := lim) (P := program) (pMain := 40) (N := N) (out := out) (bankValues := bankValues) (caps := caps) (d :=
    d) program_main program_library
end ThreeSum.LightWeightedPreparedWanted
end
end WeightedCache3SUMRefinement_e1ae71d


