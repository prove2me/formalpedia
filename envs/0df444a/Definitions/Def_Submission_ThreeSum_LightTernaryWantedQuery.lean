-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery
-- name    : Submission_ThreeSum_LightTernaryWantedQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:18:09.137661+00:00
-- url     : https://prove2.me/theorems/523f68b3-16ac-438f-ab27-f12b969548c4
-- title:
--   Light Ternary Wanted Query
-- statement:
--   Definitions and structural lemmas for Light Ternary Wanted Query, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Theorems.Thm_Light_Ends_call
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
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_program_main
import Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_address
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_lt_pow_two
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length
attribute [local simp] ThreeSum.LightTernaryFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightTernaryNearPair.program_length
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
attribute [local simp] ThreeSum.TernaryBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
structure Entries where
  near : LightTernaryNearPair.Entries
  pair : ℕ
  query : ℕ
  lookup : ℕ
structure Library (P : Program) (e : Entries) : Prop where
  near : LightTernaryNearPair.Library P e.near
  pair : P[e.pair]? = some (LightTernaryNearPair.body e.near.source e.near.product)
  query : P[e.query]? = some (LightTernaryFrozenQuery.body e.query e.lookup e.near.digit e.near.zero e.near.erase)
  lookup : P[e.lookup]? = some (LightTernaryQueryLookup.body e.near.search)
def body (e : Entries) : Stmt :=
  _root_.Light.Stmt.seq (.call e.near.rank [v 0, v 35, v 3] 37)
    (_root_.Light.Stmt.seq
      (.call e.pair
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19,
          v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33, v 34]
        38)
      (.call e.query [v 0, v 0, v 37, v 8, v 35, v 4, v 5, v 36, v 1, v 2, v 34, v 3, v 7] 0))
def args {N : ℕ} (rows out bankValues : ℕ) (f g : Config) (Q : TritWord N) : List ℤ :=
  LightTernaryNearPair.args N rows f ++ LightTernaryNearPair.args N rows g ++
    [(out : ℤ), (address Q : ℤ), (bankValues : ℤ)]
def H {N : ℕ} (F G : TritWord N → ℤ) (R : TritWord N) : ℤ :=
  ThreeSum.TernaryEuler.binomialZeta F R * ThreeSum.TernaryEuler.binomialZeta G R
def time {N : ℕ} (rows : ℕ) (f g : Config) (Q : TritWord N) : ℕ :=
  LightTernaryRank.time N + pairTime N rows f g + LightTernaryFrozenQuery.queryTime f.L f.T N Q + 300
theorem meets {e : Entries} {pMain N rows out bankValues d : ℕ} (hmain : P[pMain]? = some (body e)) (lib : Library P e)
    (f g : Config) (μ : ℕ → ℤ) (Q : TritWord N) (E : Enumeration N f.T f.nb) (nearWords : ℕ → TritWord N)
    (F G : TritWord N → ℤ) (Rf : Ready lim rows f μ Q E.word nearWords F) (Rg : Ready lim rows g μ Q E.word nearWords G)
    (hGRead : ReadBefore N rows g f.ws) (hFbeforeG : f.vals + rows ≤ g.ws) (hFout : f.vals + rows ≤ out)
    (hGout : g.vals + rows ≤ out) (hOutSpace : out + rows ≤ lim.space) (hOutKeep : f.ws ≤ out)
    (hbankBefore : bankValues + (N + 1) * f.nb ≤ f.ws)
    (hbankStages : LightTernaryBankSweep.Stages E (fun k => stageValue k (H F G)) bankValues N μ)
    (hproductWord : (f.U : ℤ) * (g.U : ℤ) ≤ lim.word)
    (hqueryWord : 4 * ((4 ^ N : ℕ) : ℤ) * ((f.U * g.U : ℕ) : ℤ) + 3 ≤ lim.word)
    (hd : d + 3 * N + f.L + 12 ≤ lim.depth) :
    Meets lim P pMain d (args rows out bankValues f g Q) μ (time rows f g Q)
      (fun v ν => v = stageValue N (H F G) Q ∧ Kept μ ν f.ws) :=
  by
  have hw := Rf.hw
  have hws : f.ws ≤ lim.space := by
    have := Rf.hmetadataRanks; have := Rf.hrankVals; have := Rf.hvals; have := Rf.hfr
    omega
  have hpSpace : f.powers + (2 * N + 1) ≤ lim.space := Rf.hp.trans hws
  have hwordPow : ((2 ^ (2 * N + 1) : ℕ) : ℤ) ≤ lim.word := by have := Rf.hword; omega
  have hscalar : ((2 * N + 16 : ℕ) : ℤ) ≤ lim.word := by have := Rf.hmemoWord; omega
  have hNword : 2 * (N : ℤ) + 3 ≤ lim.word := by have := Rf.hmemoWord; omega
  have hcutWord : (f.T : ℤ) + 1 ≤ lim.word := by have := Rf.hcontrols; omega
  have hqueryBaseWord : ((f.nb + rows + 2 ^ (2 * N + 1) + 16 : ℕ) : ℤ) ≤ lim.word := by have := Rf.hword; omega
  have hrank :=
    LightTernaryRank.meets (d := d + 1) lib.near.rank lib.near.digit lib.near.erase μ hw hpSpace hwordPow hscalar
      Rf.hpowers (address_lt_pow_two Q) (by omega)
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
    | refine _root_.Light.Ends.callToThen (hrank _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrank ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryNearPair.args,
            LightTernaryRank.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryNearPair.args, LightTernaryRank.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryNearPair.args,
            LightTernaryRank.time] <;> omega)
    on_goal -1 => (rintro rankValue μr ⟨hrankValue, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μr
  have hrankQ : rankValue = (rank Q : ℤ) := by rw [hrankValue, LightTernaryRank.partialRank_address]
  have hpair :=
    LightTernaryNearPair.meets (d := d + 1) lib.pair lib.near f g μ Q E.word nearWords F G Rf Rg hGRead hFbeforeG hFout
      hGout hOutSpace hOutKeep hproductWord (by omega)
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
    | refine _root_.Light.Ends.callToThen (hpair _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpair ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryNearPair.args,
            LightTernaryRank.time, LightTernaryNearPair.pairTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryNearPair.args, LightTernaryRank.time, LightTernaryNearPair.pairTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryNearPair.args,
            LightTernaryRank.time, LightTernaryNearPair.pairTime] <;> omega)
    on_goal -1 => (rintro result ν ⟨_, hkeep, hnearH⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hH : ∀ R, |H F G R| ≤ ((f.U * g.U : ℕ) : ℤ) := by
    intro R
    rw [H, abs_mul]
    simpa only [Nat.cast_mul] using mul_le_mul (Rf.hvalue R) (Rg.hvalue R) (abs_nonneg _) (by positivity)
  have hbankRead : ∀ j < f.nb, ν (f.bank + j) = (address (E.word j) : ℤ) :=
    by
    intro j hj
    rw [hkeep _ (by have := Rf.hb; omega)]
    exact Rf.hbankRead j hj
  have hpowers : Powers ν f.powers (2 * N) := by
    intro j hj
    rw [hkeep _ (by have := Rf.hp; omega)]
    exact Rf.hpowers j hj
  have hbankValues : ∀ k ≤ N, ∀ j < f.nb, ν (bankValues + k * f.nb + j) = stageValue k (H F G) (E.word j) :=
    by
    intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb hk
    have hs : (N + 1) * f.nb = N * f.nb + f.nb := by ring
    rw [hkeep _ (by omega)]
    exact hbankStages k hk j hj
  have hnearRead : ∀ j < rows, ν (f.a + j) = (address (nearWords j) : ℤ) :=
    by
    intro j hj
    rw [hkeep _ (by have := Rf.ha; omega)]
    exact Rf.hread j hj
  have hnearValues : ∀ j < rows, ν (out + j) = H F G (nearWords j) := hnearH
  have hquery :=
    LightTernaryFrozenQuery.meets lib.query lib.lookup lib.near.search lib.near.digit lib.near.zero lib.near.erase f.T
      f.bank f.nb bankValues f.a rows out f.powers f.L (f.U * g.U) E.word nearWords (H F G) Q ν hw (Rf.hb.trans hws)
      (hbankBefore.trans hws) (Rf.ha.trans hws) hOutSpace hpSpace hqueryBaseWord hNword hcutWord hqueryWord hpowers
      Rf.hL Rf.hnb Rf.hnn hH hbankRead Rf.hbankSorted E.complete hbankValues hnearRead Rf.hnearSorted Rf.hnearPresent
      hnearValues N le_rfl Q (fun _ => le_rfl) (d + 1) (by omega)
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
    | refine _root_.Light.Ends.callToThen (hquery _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hquery ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrankQ, LightTernaryFrozenQuery.inputs,
            LightTernaryNearPair.args, LightTernaryRank.time, LightTernaryNearPair.pairTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hrankQ, LightTernaryFrozenQuery.inputs, LightTernaryNearPair.args, LightTernaryRank.time,
              LightTernaryNearPair.pairTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrankQ, LightTernaryFrozenQuery.inputs,
            LightTernaryNearPair.args, LightTernaryRank.time, LightTernaryNearPair.pairTime] <;> omega)
    on_goal -1 => (rintro output ν' ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν'
  exact ⟨hout, hkeep⟩
def entries : Entries :=
  ⟨LightTernaryNearPair.entries, 18, 19, 20⟩
def program : Program :=
  LightTernaryNearPair.program ++
    [LightTernaryFrozenQuery.body 19 20 6 7 8, LightTernaryQueryLookup.body 10, body entries]
theorem program_library : Library program entries :=
  by
  refine ⟨?_, rfl, rfl, rfl⟩
  constructor <;> rfl
@[simp]
theorem program_main : program[21]? = some (body entries) :=
  rfl
def program_meets {N rows out bankValues d : ℕ} :=
  meets (lim := lim) (P := program) (pMain := 21) (N := N) (rows := rows) (out := out) (bankValues := bankValues) (d :=
    d) program_main program_library
end ThreeSum.LightTernaryWantedQuery


