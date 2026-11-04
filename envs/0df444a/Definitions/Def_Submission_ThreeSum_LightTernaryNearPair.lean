-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
-- name    : Submission_ThreeSum_LightTernaryNearPair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:02:34.383893+00:00
-- url     : https://prove2.me/theorems/59aeaf39-da4c-4966-bd6c-590404432b1e
-- title:
--   Light Ternary Near Pair
-- statement:
--   Definitions and structural lemmas for Light Ternary Near Pair, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearPair.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryNearSourceWords
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
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
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
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
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
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
structure Config where
  a : ℕ
  powers : ℕ
  bank : ℕ
  nb : ℕ
  bv : ℕ
  L : ℕ
  T : ℕ
  activeBase : ℕ
  ws : ℕ
  rankBase : ℕ
  vals : ℕ
  h : ℕ
  pcount : ℕ
  fr : ℕ
  U : ℕ
  V : ℕ
def args (N rows : ℕ) (c : Config) : List ℤ :=
  [N, c.a, rows, c.powers, c.bank, c.nb, c.bv, c.L, c.T, c.activeBase, c.ws, c.rankBase, c.vals, c.h, 2 * N, c.pcount,
    c.fr]
def time (N rows : ℕ) (c : Config) : ℕ :=
  LightTernaryNearSource.time N c.L rows (2 * N - c.T) c.V
structure Ready (lim : Limits) {N : ℕ} (rows : ℕ) (c : Config) (μ : ℕ → ℤ) (Q : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (source : TritWord N → ℤ) : Prop where
  homogeneous : ∀ A, source A ≠ 0 → rank A = c.h
  division : ∀ current, c.T < current → current ≤ 2 * N → Light.Emod.Pre lim (current - c.h) c.V c.fr
  hw : (lim.space : ℤ) ≤ lim.word
  ha : c.a + rows ≤ c.ws
  hb : c.bank + c.nb ≤ c.ws
  hp : c.powers + (2 * N + 1) ≤ c.ws
  hactiveSpace : c.activeBase + N ≤ c.ws
  hbankVals : c.bv + c.nb ≤ c.ws
  hmetadataRanks : c.ws + 2 * N * rows + N ≤ c.rankBase
  hrankVals : c.rankBase + rows ≤ c.vals
  hvals : c.vals + rows ≤ c.fr
  hfr : c.fr ≤ lim.space
  hcount : c.vals + rows ≤ c.pcount
  hspace : c.pcount ≤ lim.space
  hword : ((c.nb + rows + 2 ^ (2 * N + 1) + 2 * N + 32 : ℕ) : ℤ) ≤ lim.word
  hcontrols : ((c.T + N + 32 : ℕ) : ℤ) ≤ lim.word
  hmemoWord : ((N + rows + 2 * N + c.h + 20 : ℕ) : ℤ) ≤ lim.word
  hread : ∀ j < rows, μ (c.a + j) = (address (nearWords j) : ℤ)
  hbankRead : ∀ j < c.nb, μ (c.bank + j) = (address (bankWords j) : ℤ)
  hactiveRead : ∀ i < N, μ (c.activeBase + i) = 1
  hbankSorted : ∀ j k, j < k → k < c.nb → address (bankWords j) < address (bankWords k)
  hnearSorted : ∀ j k, j < k → k < rows → address (nearWords j) < address (nearWords k)
  hpowers : Powers μ c.powers (2 * N)
  hL : c.L ≤ 2 * N
  hnb : c.nb < 2 ^ c.L
  hnn : rows < 2 ^ c.L
  hnbpos : 0 < c.nb
  hbankPresent : ∀ W, rank W ≤ c.T → ∃ j < c.nb, bankWords j = W
  hnearPresent : ∀ W, Below W Q → c.T < rank W → ∃ j < rows, nearWords j = W
  hnearRows : ∀ j < rows, Below (nearWords j) Q ∧ c.T < rank (nearWords j)
  hT : c.T ≤ 2 * N
  hh : c.h ≤ c.T
  hbankValues : ∀ j < c.nb, μ (c.bv + j) = binomialZeta source (bankWords j)
  hvalue : ∀ R, |binomialZeta source R| ≤ c.U
  hV : 2 * (N + 1) * c.U ≤ c.V
def ReadBefore (N rows : ℕ) (c : Config) (cut : ℕ) : Prop :=
  c.a + rows ≤ cut ∧ c.bank + c.nb ≤ cut ∧ c.powers + (2 * N + 1) ≤ cut ∧ c.activeBase + N ≤ cut ∧ c.bv + c.nb ≤ cut
theorem Ready.transfer {lim : Limits} {N rows cut : ℕ} {c : Config} {μ ν : ℕ → ℤ} {Q : TritWord N}
    {bankWords nearWords : ℕ → TritWord N} {source : TritWord N → ℤ}
    (R : Ready lim rows c μ Q bankWords nearWords source) (H : Kept μ ν cut) (B : ReadBefore N rows c cut) :
    Ready lim rows c ν Q bankWords nearWords source :=
  by
  refine { R with hread := ?_, hbankRead := ?_, hactiveRead := ?_, hpowers := ?_, hbankValues := ?_ }
  · intro j hj; rw [H _ (by rcases B with ⟨h, _, _, _, _⟩; omega)]; exact R.hread j hj
  · intro j hj; rw [H _ (by rcases B with ⟨_, h, _, _, _⟩; omega)]; exact R.hbankRead j hj
  · intro i hi; rw [H _ (by rcases B with ⟨_, _, _, h, _⟩; omega)]; exact R.hactiveRead i hi
  · intro i hi; rw [H _ (by rcases B with ⟨_, _, h, _, _⟩; omega)]; exact R.hpowers i hi
  · intro j hj; rw [H _ (by rcases B with ⟨_, _, _, _, h⟩; omega)]; exact R.hbankValues j hj
structure Entries where
  source : ℕ
  ranks : ℕ
  metadata : ℕ
  memo : ℕ
  column : ℕ
  cell : ℕ
  digit : ℕ
  zero : ℕ
  erase : ℕ
  rank : ℕ
  search : ℕ
  scan : ℕ
  fill : ℕ
  row : ℕ
  sum : ℕ
  divide : ℕ
  natural : ℕ
  product : ℕ
structure Library (P : Program) (e : Entries) : Prop where
  source : P[e.source]? = some (LightTernaryNearSource.body e.ranks e.metadata e.memo)
  ranks : P[e.ranks]? = some (LightTernaryRankTable.body e.rank)
  metadata : P[e.metadata]? = some (LightTernaryEulerMetadata.body e.column)
  memo : P[e.memo]? = some (LightTernaryEulerMemo.body e.scan)
  column : P[e.column]? = some (LightTernaryPredecessorTable.body e.cell e.digit)
  cell : P[e.cell]? = some (LightTernaryPredecessor.body e.digit e.zero e.erase e.rank e.search)
  digit : P[e.digit]? = some (LightTernaryCodes.digitBody e.erase)
  zero : P[e.zero]? = some (LightTernaryCodes.zeroBody e.erase)
  erase : P[e.erase]? = some (LightMaskErase.body e.erase)
  rank : P[e.rank]? = some (LightTernaryRank.body e.digit)
  search : P[e.search]? = some (LightBandLookup.searchBody e.search)
  scan : P[e.scan]? = some (LightTernaryEulerScan.body e.fill)
  fill : P[e.fill]? = some (LightTernaryEulerRow.fillBody e.row)
  row : P[e.row]? = some (LightTernaryEulerRow.body e.sum e.divide)
  sum : P[e.sum]? = some LightTernaryWeightedSum.body
  divide : P[e.divide]? = some (LightTernaryDivide.body e.natural)
  natural : P[e.natural]? = some LightOutputDecodeDivide.body
  product : P[e.product]? = some LightTernaryProduct.body
theorem Ready.meets {lim : Limits} {P : Program} {e : Entries} (lib : Library P e) {N rows d : ℕ} {c : Config}
    {μ : ℕ → ℤ} {Q : TritWord N} {bankWords nearWords : ℕ → TritWord N} {source : TritWord N → ℤ}
    (R : Ready lim rows c μ Q bankWords nearWords source) (hd : d + 2 * N + 7 ≤ lim.depth) :
    Meets lim P e.source d (args N rows c) μ (time N rows c)
      (fun r ν => r = 0 ∧ Kept μ ν c.ws ∧ ∀ j < rows, ν (c.vals + j) = binomialZeta source (nearWords j)) :=
  by
  exact
    LightTernaryNearSourceWords.meets lib.source lib.ranks lib.metadata lib.memo lib.column lib.cell lib.digit lib.zero
      lib.erase lib.rank lib.search lib.scan lib.fill lib.row lib.sum lib.divide lib.natural μ Q bankWords nearWords
      source R.homogeneous R.division R.hw R.ha R.hb R.hp R.hactiveSpace R.hbankVals R.hmetadataRanks R.hrankVals
      R.hvals R.hfr R.hcount R.hspace R.hword R.hcontrols R.hmemoWord R.hread R.hbankRead R.hactiveRead R.hbankSorted
      R.hnearSorted R.hpowers R.hL R.hnb R.hnn R.hnbpos R.hbankPresent R.hnearPresent R.hnearRows R.hT R.hh
      R.hbankValues R.hvalue R.hV hd
def body (pSource pProduct : ℕ) : Stmt :=
  _root_.Light.Stmt.seq
    (.call pSource [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16] 35)
    (_root_.Light.Stmt.seq
      (.call pSource
        [v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33] 35)
      (_root_.Light.Stmt.seq (.call pProduct [v 12, v 29, v 34, v 2] 35) (.set 0 (k 0))))
def pairTime (N rows : ℕ) (f g : Config) : ℕ :=
  time N rows f + time N rows g + LightTernaryProduct.time rows + 1000
theorem meets {lim : Limits} {P : Program} {e : Entries} {pMain N rows out d : ℕ}
    (hmain : P[pMain]? = some (body e.source e.product)) (lib : Library P e) (f g : Config) (μ : ℕ → ℤ) (Q : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (F G : TritWord N → ℤ) (Rf : Ready lim rows f μ Q bankWords nearWords F)
    (Rg : Ready lim rows g μ Q bankWords nearWords G) (hGRead : ReadBefore N rows g f.ws)
    (hFbeforeG : f.vals + rows ≤ g.ws) (hFout : f.vals + rows ≤ out) (hGout : g.vals + rows ≤ out)
    (hOutSpace : out + rows ≤ lim.space) (hOutKeep : f.ws ≤ out) (hvalue : (f.U : ℤ) * (g.U : ℤ) ≤ lim.word)
    (hd : d + 2 * N + 8 ≤ lim.depth) :
    Meets lim P pMain d (args N rows f ++ args N rows g ++ [(out : ℤ)]) μ (pairTime N rows f g)
      (fun r ν =>
        r = 0 ∧
          Kept μ ν f.ws ∧ ∀ j < rows, ν (out + j) = binomialZeta F (nearWords j) * binomialZeta G (nearWords j)) :=
  by
  have hw := Rf.hw
  have hfmeta := Rf.hmetadataRanks
  have hfrank := Rf.hrankVals
  have hFws : f.ws ≤ f.vals := by omega
  have hcF := Rf.meets lib (d := d + 1) (by omega)
  apply Meets.of_body hmain
  unfold body pairTime
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
    | refine _root_.Light.Ends.callToThen (hcF _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcF ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, time, LightTernaryNearSource.time,
            LightTernaryProduct.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, time, LightTernaryNearSource.time, LightTernaryProduct.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, time, LightTernaryNearSource.time,
            LightTernaryProduct.time] <;> omega)
    on_goal -1 => (rintro rf ν ⟨hrf, hkeepF, hF⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have RG := Rg.transfer hkeepF hGRead
  have hcG := RG.meets lib (d := d + 1) (by omega)
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
    | refine _root_.Light.Ends.callToThen (hcG _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcG ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, time, LightTernaryNearSource.time,
            LightTernaryProduct.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, time, LightTernaryNearSource.time, LightTernaryProduct.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, time, LightTernaryNearSource.time,
            LightTernaryProduct.time] <;> omega)
    on_goal -1 => (rintro rg ξ ⟨hrg, hkeepG, hG⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hfRead : ∀ j < rows, ξ (f.vals + j) = binomialZeta F (nearWords j) := by
    intro j hj
    rw [hkeepG _ (by omega), hF j hj]
  have hp :=
    LightTernaryProduct.meets (d := d + 1) lib.product ξ Rf.hw (by omega) (by omega) hOutSpace (Or.inr (Or.inl hFout))
      (Or.inr (Or.inl hGout)) (fun j hj => by rw [hfRead j hj]; exact Rf.hvalue _)
      (fun j hj => by rw [hG j hj]; exact Rg.hvalue _) hvalue
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, time, LightTernaryNearSource.time,
            LightTernaryProduct.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, time, LightTernaryNearSource.time, LightTernaryProduct.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, time, LightTernaryNearSource.time,
            LightTernaryProduct.time] <;> omega)
    on_goal -1 => (rintro rp η ⟨hProducts, hOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, args, time, LightTernaryNearSource.time,
            LightTernaryProduct.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [args, time, LightTernaryNearSource.time, LightTernaryProduct.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, args, time, LightTernaryNearSource.time,
            LightTernaryProduct.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    change η x = μ x
    rw [hOutside x (Or.inl (by omega)), hkeepG x (by omega), hkeepF x hx]
  · intro j hj
    change η (out + j) = _
    rw [hProducts j hj, hfRead j hj, hG j hj]
def entries : Entries :=
  ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17⟩
def program : Program :=
  [LightTernaryNearSource.body 1 2 3, LightTernaryRankTable.body 9, LightTernaryEulerMetadata.body 4,
    LightTernaryEulerMemo.body 11, LightTernaryPredecessorTable.body 5 6, LightTernaryPredecessor.body 6 7 8 9 10,
    LightTernaryCodes.digitBody 8, LightTernaryCodes.zeroBody 8, LightMaskErase.body 8, LightTernaryRank.body 6,
    LightBandLookup.searchBody 10, LightTernaryEulerScan.body 12, LightTernaryEulerRow.fillBody 13,
    LightTernaryEulerRow.body 14 15, LightTernaryWeightedSum.body, LightTernaryDivide.body 16,
    LightOutputDecodeDivide.body, LightTernaryProduct.body, body 0 17]
theorem program_library : Library program entries := by constructor <;> rfl
@[simp]
theorem program_main : program[18]? = some (body entries.source entries.product) :=
  rfl
def program_meets {lim : Limits} {N rows out d : ℕ} :=
  meets (lim := lim) (N := N) (rows := rows) (out := out) (d := d) program_main program_library
end ThreeSum.LightTernaryNearPair


