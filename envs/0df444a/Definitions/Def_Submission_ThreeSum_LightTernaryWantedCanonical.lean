-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
-- name    : Submission_ThreeSum_LightTernaryWantedCanonical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:00:22.72602+00:00
-- url     : https://prove2.me/theorems/82d3789d-e93f-499d-85de-5ba154775145
-- title:
--   Light Ternary Wanted Canonical
-- statement:
--   Definitions and structural lemmas for Light Ternary Wanted Canonical, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean

import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_append
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_base
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_child_target_bound
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_base
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedRadix_localBucket_eq_of_emod
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedOutputs_length_le
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_append
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket


set_option autoImplicit false
namespace ThreeSum.LightTernaryWantedCanonical
open Light
open TernaryWantedRadix (localBucket mem_localBucket localBucket_eq_of_emod wantedOutputs wantedOutputs_length_le child_target_bound codeLimit codeLimit_base codeLimit_child)
open TernaryWantedLittleEndian (wantedCodes wantedCodes_length wantedCodes_succ encode)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
def recordSteps (pSelf pDivide P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : List ℕ → Stmt
  | [] => .skip
  | i::is =>
      .call pDivide [v 1 -' LightSignedFiniteTable.literal (raws.getD i 0),k P,v 8] 9 ;;
      .call pSelf [v 0 -' k 1,v 9,v 2 +' v 3 *' k (words.getD i 0),v 3 *' k R,
        v 4 +' v 5 *' k (maps.getD i 0),v 5 *' k S,v 6,v 10,v 8] 10 ;;
      recordSteps pSelf pDivide P R S raws words maps is
def selector (pSelf pDivide P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : List ℕ → Stmt
  | [] => .skip
  | r::rs => .ite (v 11 =' k r)
      (recordSteps pSelf pDivide P R S raws words maps (localBucket (P : ℤ) raws (r : ℤ)))
      (selector pSelf pDivide P R S raws words maps rs)
def body (pSelf pDivide pEmod P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.call pEmod [v 1,k P,v 8] 11 ;;
      .set 10 (v 7) ;;
      selector pSelf pDivide P R S raws words maps (List.range P) ;;
      .set 0 (v 10))
    (.store (v 7) (v 6) ;;
      .store (v 7 +' k 1) (v 2) ;;
      .store (v 7 +' k 2) (v 4) ;;
      .set 0 (v 7 +' k 3))
def program (P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  [body 0 1 3 P R S raws words maps,LightTernaryDivide.body 2,LightOutputDecodeDivide.body,emodBody]
def overhead (P V : ℕ) : ℕ := LightResidues.residueBudget (2*V)+10*P+40
def stepCost (V : ℕ) : ℕ := LightTernaryDivide.time (2*V)+100
def time (P C V : ℕ) : ℕ → ℕ
  | 0 => 40
  | j+1 => overhead P V+C*(stepCost V+time P C V j)
variable {lim : Limits} {Prog : Program} {d : ℕ}
abbrev rowCells := TernaryWantedCanonicalPairs.rowCells
abbrev rowCells_length := TernaryWantedCanonicalPairs.rowCells_length
abbrev rowCells_append := TernaryWantedCanonicalPairs.rowCells_append
def branchCodes (P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ) (x : ℤ) (code scale mapCode mapScale : ℕ)
    (is : List ℕ) : List (ℕ × ℕ) := is.flatMap fun i =>
      wantedCodes (P : ℤ) raws words maps j ((x-raws.getD i 0)/(P : ℤ))
        R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S)
end ThreeSum.LightTernaryWantedCanonical


