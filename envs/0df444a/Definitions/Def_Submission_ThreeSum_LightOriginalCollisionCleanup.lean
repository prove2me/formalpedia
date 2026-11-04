-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
-- name    : Submission_ThreeSum_LightOriginalCollisionCleanup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:37:02.950207+00:00
-- url     : https://prove2.me/theorems/a2ee3595-9371-4210-a9a3-dd3ed4e8f89b
-- title:
--   Light Original Collision Cleanup
-- statement:
--   Definitions and structural lemmas for Light Original Collision Cleanup, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightColoredTwoSum_meets
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_lengths
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
attribute [local simp] ThreeSum.LightDeletedTwoSum.flag_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightOriginalCollisionCleanup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightOriginalBucketFilter
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
def counts (keys : ℕ → ℕ) (n r : ℕ) : ℕ :=
  LightHistogram.count keys r n
def badIndices (keys : ℕ → ℕ) (n : ℕ) : List ℕ :=
  bad keys (counts keys n) n
def badIndex (keys : ℕ → ℕ) (n j : ℕ) : ℕ :=
  if hj : j < (badIndices keys n).length then (badIndices keys n)[j] else 0
theorem badIndex_lt {keys : ℕ → ℕ} {n j : ℕ} (hj : j < (badIndices keys n).length) : badIndex keys n j < n :=
  by
  have hm := List.getElem_mem hj
  have hh := List.mem_filter.mp hm
  have hr := List.mem_range.mp hh.1
  simpa only [badIndex, dif_pos hj] using hr
def body (pFilter pCleanup : ℕ) : Stmt :=
  _root_.Light.Stmt.seq (.call pFilter [v 0, v 1, v 2, v 3, v 4] 13)
    (.call pCleanup
      [(_root_.Light.Expr.op _root_.Light.Op.add) (v 4) (v 1), v 13, v 5, v 1, v 6, v 7, v 8, v 9, v 10, v 11, v 12] 0)
def time (keys : ℕ → ℕ) (n scanN L : ℕ) : ℕ :=
  LightOriginalBucketFilter.time n + LightDeletedTwoSum.time (badIndices keys n).length scanN L + 200
variable {lim : Limits} {P : Program}
theorem meets
    {pMain pFilter pCleanup pTwoSum pLookup pSearch keyBase n hist q out valuesBase scanBase scanN targetBase targetN
      powers W L U d : ℕ}
    (sign : ℤ) (hmain : P[pMain]? = some (body pFilter pCleanup))
    (hfilter : P[pFilter]? = some LightOriginalBucketFilter.body)
    (hcleanup : P[pCleanup]? = some (LightDeletedTwoSum.body pTwoSum))
    (htwo : P[pTwoSum]? = some (LightColoredTwoSum.body pLookup))
    (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ) (keys : ℕ → ℕ)
    (values scan target : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hkeysSpace : keyBase + n ≤ out)
    (hhistSpace : hist + q ≤ out) (hout : out + 2 * n ≤ lim.space) (hvaluesSpace : valuesBase + n ≤ out)
    (hscanSpace : scanBase + scanN ≤ out) (htargetSpace : targetBase + targetN ≤ out) (hspace : powers + (W + 1) ≤ out)
    (hword : ((targetN + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hkeys : ∀ i < n, keys i < q)
    (hreadKeys : ∀ i < n, μ (keyBase + i) = (keys i : ℤ)) (hcounts : ∀ k < q, μ (hist + k) = (counts keys n k : ℤ))
    (hvalues : ∀ i < n, |values i| ≤ U) (hreadValues : ∀ i < n, μ (valuesBase + i) = values i)
    (hscan : ∀ i < scanN, |scan i| ≤ U) (hreadScan : ∀ i < scanN, μ (scanBase + i) = scan i)
    (hreadTarget : ∀ i < targetN, μ (targetBase + i) = target i) (hsign : |sign| ≤ 1)
    (hvalueWord : 2 * (U : ℤ) + 3 ≤ lim.word) (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i < j → j < targetN → target i < target j) (hL : L ≤ W) (htargetN : targetN < 2 ^ L)
    (hd : d + L + 4 ≤ lim.depth) :
    Meets lim P pMain d [keyBase, n, hist, q, out, valuesBase, scanBase, scanN, targetBase, targetN, powers, L, sign] μ
      (time keys n scanN L)
      (fun r ν =>
        r =
            (LightDeletedTwoSum.flag (badIndex keys n) values scan target targetN scanN (badIndices keys n).length
                sign :
              ℤ) ∧
          Seg ν out (cells (good keys (counts keys n) n)) ∧
            Seg ν (out + n) (cells (badIndices keys n)) ∧ SameOutside μ ν out (2 * n)) :=
  by
  have hnword : (n : ℤ) ≤ lim.word := by omega
  have hcword : ∀ k < q, (counts keys n k : ℤ) ≤ lim.word :=
    by
    intro k hk
    exact (Int.ofNat_le.mpr (LightHistogram.count_le keys k n)).trans hnword
  have hf :=
    LightOriginalBucketFilter.meets (d := d + 1) hfilter μ keys (counts keys n) hw hkeysSpace hhistSpace hout hkeys
      hreadKeys hcounts hcword (by omega)
  apply Meets.of_body hmain
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hf _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hf ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOriginalBucketFilter.time, LightDeletedTwoSum.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time] <;>
          omega)
    on_goal -1 => (rintro badN ν ⟨hBadN, hGood, hBad, H⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  change badN = ((badIndices keys n).length : ℤ) at hBadN
  have hKeep {x : ℕ} (hx : x < out) : ν x = μ x := H x (Or.inl hx)
  have hIdRead : ∀ i < (badIndices keys n).length, ν (out + n + i) = (badIndex keys n i : ℤ) :=
    by
    intro i hi
    have hh := hBad i (by simpa [cells, badIndices] using hi)
    rw [badIndex, dif_pos hi]
    simpa [cells, List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, List.getElem_map, badIndices] using hh
  have hPowers : Powers ν powers W := by intro i hi; rw [hKeep (by omega), hpowers i hi]
  have hBadLen : (badIndices keys n).length ≤ n := (lengths keys (counts keys n) n).2
  have hc :=
    LightDeletedTwoSum.meets (d := d + 1) (badBase := out + n) (badN := (badIndices keys n).length) (valuesBase :=
      valuesBase) (originalN := n) (scanBase := scanBase) (scanN := scanN) (targetBase := targetBase) (targetN :=
      targetN) (powers := powers) (W := W) (L := L) (U := U) sign hcleanup htwo hlookup hsearch ν (badIndex keys n)
      values scan target hw (by omega) (by omega) (by omega) (by omega) (by omega) hword (fun i hi => badIndex_lt hi)
      hIdRead hvalues (fun i hi => by rw [hKeep (by omega), hreadValues i hi]) hscan
      (fun i hi => by rw [hKeep (by omega), hreadScan i hi]) (fun i hi => by rw [hKeep (by omega), hreadTarget i hi])
      hsign hvalueWord hPowers hsorted hL htargetN (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hBadN, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hBadN, LightOriginalBucketFilter.time, LightDeletedTwoSum.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hBadN, LightOriginalBucketFilter.time,
            LightDeletedTwoSum.time] <;>
          omega)
    on_goal -1 => (rintro result ξ ⟨hResult, hMem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ξ
  refine ⟨?_, hGood, hBad, H⟩
  change result = _
  exact hResult
def program : Program :=
  [body 1 2, LightOriginalBucketFilter.body, LightDeletedTwoSum.body 3, LightColoredTwoSum.body 4,
    LightBandLookup.body 5, LightBandLookup.searchBody 5]
def program_meets {lim : Limits} {keyBase n hist q out valuesBase scanBase scanN targetBase targetN powers W L U d : ℕ}
    (sign : ℤ) :=
  meets (lim := lim) (P := program) (pMain := 0) (pFilter := 1) (pCleanup := 2) (pTwoSum := 3) (pLookup := 4)
    (pSearch := 5) (keyBase := keyBase) (n := n) (hist := hist) (q := q) (out := out) (valuesBase := valuesBase)
    (scanBase := scanBase) (scanN := scanN) (targetBase := targetBase) (targetN := targetN) (powers := powers) (W := W)
    (L := L) (U := U) (d := d) sign rfl rfl rfl rfl rfl rfl
end ThreeSum.LightOriginalCollisionCleanup


