-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingCatalogBatch
-- name    : Submission_ThreeSum_LightReportingCatalogBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:22:52.4159+00:00
-- url     : https://prove2.me/theorems/f1676b8b-6597-4900-8dd2-34661cdb05c0
-- title:
--   Light Reporting Catalog Batch
-- statement:
--   Definitions and structural lemmas for Light Reporting Catalog Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogBatch.lean

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixValueBounds
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightReportingCatalogBatch
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def roundBody (pQuery : ℕ) : Stmt :=
  .set 23 (M (v 16 +' v 22)) ;;
  .set 24 (M (v 17 +' v 22)) ;;
  .call pQuery [v 0,v 1,v 2,v 3,v 23,v 4,v 24,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    v 13,v 14,v 15,v 20,v 21] 25 ;;
  .store (v 19 +' v 22) (v 25)
def body (pQuery : ℕ) : Stmt := .for 22 (v 18) (roundBody pQuery)
def program : Program := LightReportingCatalogQuery.program ++ [body 35]
def time (h J k t n : ℕ) : ℕ := n*(LightReportingCatalogQuery.time h J k t+180)+30
def Inv (μ : ℕ → ℤ) (counts : ℕ → ℕ)
    (h J k t Qmask baseL baseR boxCut indexBase ptrBase inL inR n dst maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,k*h,
      suffixStage J (512*h) k,k*(512*h),residualSize h J k,Qmask,t,baseL,baseR,
      boxCut,indexBase,ptrBase,count h k,inL,inR,n,dst,maskBase,work,j,a,b,r],μ'⟩ ∧
    (∀ i < j, μ' (dst+i) = (counts i : ℤ)) ∧ KeptBut μ μ' maskBase dst n
end ThreeSum.LightReportingCatalogBatch


