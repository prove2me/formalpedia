-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingPairRows
-- name    : Submission_ThreeSum_LightReportingPairRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:43:24.350184+00:00
-- url     : https://prove2.me/theorems/1f6c4ecc-8159-42b9-992a-b1c55cc04e1b
-- title:
--   Light Reporting Pair Rows
-- statement:
--   Definitions and structural lemmas for Light Reporting Pair Rows, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPairRows.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingPairRows
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration
set_option maxHeartbeats 1800000
variable {lim : Limits}
def roundBody (pQuery pAffine : ℕ) : Stmt :=
  .set 10 (M (v 2 +' v 9)) ;;
  .set 11 (v 7 -' v 10) ;;
  .call pQuery [v 0,v 11,v 1,v 4 +' v 8,v 5] 12 ;;
  .call pAffine [v 4 +' v 8,v 3 +' v 8,v 12,v 10,k 0] 13 ;;
  .set 8 (v 8 +' v 12)
def body (pLayer pQuery pAffine : ℕ) : Stmt :=
  .call pLayer [v 0,v 1,v 2,v 5] 6 ;;
  .set 7 (M (v 5 +' v 0) -' k 1) ;;
  .set 8 (k 0) ;;
  .for 9 (v 6) (roundBody pQuery pAffine) ;;
  .set 0 (v 8)
def program : Program := LightQueryEnumeration.program ++
  [LightSubsetEnumerationSetup.body 2 4,LightReportingAffine.body,body 5 0 6]
def roundTime (L h : ℕ) : ℕ :=
  LightQueryEnumeration.time L (L-h) h+LightReportingAffine.time ((L-h).choose h)+220
def time (L h : ℕ) : ℕ :=
  LightSubsetEnumerationSetup.time L h+L.choose h*(roundTime L h+20)+130
def Inv (μ : ℕ → ℤ) (L h srcS dstL dstR work j : ℕ) (σ : State) : Prop :=
  ∃ (a b nr r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,h,srcS,dstL,dstR,work,L.choose h,subsetMask (Finset.univ : Finset (Fin L)),
      j*(L-h).choose h,j,a,b,nr,r],μ'⟩ ∧
    SegN μ' srcS (enumerateLayer L h) ∧
    (∀ i < j, ∀ l < (L-h).choose h,
      μ' (dstL+i*(L-h).choose h+l) = (subsetMask (leftAt L h i) : ℤ) ∧
      μ' (dstR+i*(L-h).choose h+l) = (subsetMask (rightAt L h i l) : ℤ)) ∧
    Kept μ μ' srcS
end ThreeSum.LightReportingPairRows


