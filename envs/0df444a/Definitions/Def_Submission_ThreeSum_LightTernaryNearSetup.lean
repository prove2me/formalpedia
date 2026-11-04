-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryNearSetup
-- name    : Submission_ThreeSum_LightTernaryNearSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:17:54.55838+00:00
-- url     : https://prove2.me/theorems/55755519-b1b8-4fc6-a464-c17989dd0d03
-- title:
--   Light Ternary Near Setup
-- statement:
--   Definitions and structural lemmas for Light Ternary Near Setup, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSetup.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryNearDigits
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
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
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_pow_two_even
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryNearDigits_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
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
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_lt_pow_two
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
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
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.output_length
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
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
set_option autoImplicit false
namespace ThreeSum.LightTernaryNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBankEnumeration ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
def body (pPowers pDigits pEnum : ℕ) : Stmt :=
  _root_.Light.Stmt.seq
    (.call pPowers
      [v 4, (_root_.Light.Expr.op _root_.Light.Op.add) ((_root_.Light.Expr.op _root_.Light.Op.mul) (k 2) (v 0)) (k 1),
        k 2]
      7)
    (_root_.Light.Stmt.seq (.call pDigits [v 0, v 2, v 4, v 5, v 6] 7) (.call pEnum [v 0, v 1, k 0, v 3, v 4, v 5] 0))
def time {N : ℕ} (Q : TritWord N) (D : ℕ) : ℕ :=
  powTableTime (2 * N + 1) + LightTernaryNearDigits.time N + LightTernaryNearEnumeration.time (wordList Q) D + 300
variable {lim : Limits} {P : Program}
theorem meets {pMain pPowers pDigits pDigit pErase pEnum pBranch N D dst powers caps active d : ℕ}
    (hmain : P[pMain]? = some (body pPowers pDigits pEnum)) (hpowers : P[pPowers]? = some powTableBody)
    (hdigits : P[pDigits]? = some (LightTernaryNearDigits.body pDigit))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (henum : P[pEnum]? = some (LightTernaryNearEnumeration.body pBranch))
    (hbranch : P[pBranch]? = some (LightTernaryNearEnumeration.branchBody pEnum)) (μ : ℕ → ℤ) (Q : TritWord N)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers + (2 * N + 1) ≤ lim.space)
    (hword : ((4 ^ (N + 1) : ℕ) : ℤ) ≤ lim.word) (hD : D ≤ 2 * N)
    (hdst : dst + (TernaryNearEnumeration.codes (wordList Q) D).length ≤ caps) (hcaps : caps + N ≤ active)
    (hactive : active + N ≤ powers) (hd : d + 2 * N + 3 ≤ lim.depth) :
    Meets lim P pMain d [N, D, address Q, dst, powers, caps, active] μ (time Q D)
      (fun r ν =>
        r = ((TernaryNearEnumeration.codes (wordList Q) D).length : ℤ) ∧
          Seg ν dst ((TernaryNearEnumeration.codes (wordList Q) D).map (fun c => (c : ℤ))) ∧
            Powers ν powers (2 * N) ∧ (∀ i < N, ν (active + i) = 1) ∧ Kept μ ν dst) :=
  by
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hp : 0 < (4 : ℕ) ^ N := by positivity
    have hb : (2 : ℕ) ≤ 4 ^ (N + 1) := by rw [pow_succ]; omega
    exact (Int.ofNat_le.mpr hb).trans hword
  have hRows :
    (TernaryNearEnumeration.codes (wordList Q) D).length = (TernaryNearEnumeration.words (wordList Q) D).length :=
    TernaryNearEnumeration.codes_length _ _
  have hpowBound : ∀ j ≤ 2 * N + 1, ((2 ^ j : ℕ) : ℤ) ≤ lim.word :=
    by
    intro j hj
    have hle : 2 ^ j ≤ 4 ^ (N + 1) := by
      rw [← LightTernaryEnumeration.pow_two_even]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Int.ofNat_le.mpr hle).trans hword
  have hpow :=
    powTable_meets (d := d + 1) (μ := μ) (dst := powers) (L := 2 * N + 1) (b := 2) hpowers hw hspace hpowBound
  apply Meets.of_body hmain
  unfold body time
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
    | refine _root_.Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpow ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightTernaryNearDigits.time,
            LightTernaryNearEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightTernaryNearDigits.time, LightTernaryNearEnumeration.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightTernaryNearDigits.time,
            LightTernaryNearEnumeration.time] <;> omega)
    on_goal -1 => (rintro rp ν ⟨hPowSeg, hPowOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hPowers := powers_of_segment hPowSeg
  have hdCall :=
    LightTernaryNearDigits.meets (d := d + 1) hdigits hdigit herase ν hw hspace (hpowBound _ le_rfl)
      (address_lt_pow_two Q) hcaps hactive hPowers (by omega)
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
    | refine _root_.Light.Ends.callToThen (hdCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hdCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightTernaryNearDigits.time,
            LightTernaryNearEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightTernaryNearDigits.time, LightTernaryNearEnumeration.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightTernaryNearDigits.time,
            LightTernaryNearEnumeration.time] <;> omega)
    on_goal -1 =>
      (rintro rd ξ ⟨hCaps, hActive, hDigitsOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hSpan : caps + (active + N - caps) = active + N := Nat.add_sub_of_le (by omega)
  have hPowers' : Powers ξ powers (2 * N) := by
    intro i hi
    rw [hDigitsOutside _ (Or.inr (by omega))]
    exact hPowers i hi
  have hCapsSeg : Seg ξ caps ((wordList Q).map (fun q => (q : ℤ))) :=
    by
    intro i hi
    have hin : i < N := by
      simpa only [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, List.length_map, wordList_length] using hi
    have he : LightTernaryRank.digitAt N (address Q) i = (Q ⟨i, hin⟩).val := digit_eq Q ⟨i, hin⟩
    simpa [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, wordList, List.getElem_map, he] using hCaps i hin
  have hEnumCall :=
    LightTernaryNearEnumerationMain.meets henum hbranch hw hspace hword (wordList Q) D 0 dst caps ξ (wordList_digits Q)
      (by simp) hD (by simp) (by omega) (by omega) (by simp; omega) hPowers' hCapsSeg (d + 1)
      (by simp only [wordList_length]; omega)
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
    | refine _root_.Light.Ends.callToThen (hEnumCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hEnumCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightTernaryNearDigits.time,
            LightTernaryNearEnumeration.time, wordList_length]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightTernaryNearDigits.time, LightTernaryNearEnumeration.time, wordList_length] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightTernaryNearDigits.time,
            LightTernaryNearEnumeration.time, wordList_length] <;> omega)
    on_goal -1 =>
      (rintro result η ⟨hCount, hSeg, hEnumOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change result = ((TernaryNearEnumeration.codes (wordList Q) D).length : ℤ)
    simpa only [← hRows] using hCount
  ·
    simpa [LightTernaryNearEnumeration.output, TernaryNearEnumeration.codes_eq_map, List.bind_eq_flatMap, List.pure_def,
      ← List.map_eq_flatMap, List.map_map, Function.comp_def] using hSeg
  · intro i hi
    change η (powers + i) = _
    rw [hEnumOutside _ (Or.inr (by omega))]
    exact hPowers' i hi
  · intro i hi
    change η (active + i) = 1
    rw [hEnumOutside _ (Or.inr (by omega))]
    exact hActive i hi
  · intro x hx
    change η x = μ x
    rw [hEnumOutside _ (Or.inl hx), hDigitsOutside _ (Or.inl (by omega)), hPowOutside _ (Or.inl (by omega))]
def program : Program :=
  [body 1 2 5, powTableBody, LightTernaryNearDigits.body 3, LightTernaryCodes.digitBody 4, LightMaskErase.body 4,
    LightTernaryNearEnumeration.body 6, LightTernaryNearEnumeration.branchBody 5]
def program_meets {lim : Limits} {N D dst powers caps active d : ℕ} :=
  meets (lim := lim) (N := N) (D := D) (dst := dst) (powers := powers) (caps := caps) (active := active) (d := d) (P :=
    program) (pMain := 0) (pPowers := 1) (pDigits := 2) (pDigit := 3) (pErase := 4) (pEnum := 5) (pBranch := 6) rfl rfl
    rfl rfl rfl rfl rfl
end ThreeSum.LightTernaryNearSetup


