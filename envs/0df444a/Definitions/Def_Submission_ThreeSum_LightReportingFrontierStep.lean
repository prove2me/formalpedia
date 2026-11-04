-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingFrontierStep
-- name    : Submission_ThreeSum_LightReportingFrontierStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:51:23.899412+00:00
-- url     : https://prove2.me/theorems/741b8469-eb9b-4e7e-b4c0-8865032128ea
-- title:
--   Light Reporting Frontier Step
-- statement:
--   Definitions and structural lemmas for Light Reporting Frontier Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFrontierStep.lean

import Definitions.Def_Submission_ThreeSum_LightReportingPositiveExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostPositiveBatch
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingFrontierStep
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive ReportingHostPositiveBatch
open LightReportingPositiveExpand
set_option maxHeartbeats 3500000
set_option maxRecDepth 10000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def roundBody (pExpand : ℕ) : Stmt :=
  .set 31 (M (v 24 +' v 30)) ;;
  .set 32 (M (v 25 +' v 30)) ;;
  .call pExpand [v 0,v 1,v 2,v 31,v 32,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 27 +' v 29,v 28 +' v 29] 33 ;;
  .set 29 (v 29 +' v 33)
def body (pExpand : ℕ) : Stmt :=
  .set 29 (k 0) ;; .for 30 (v 26) (roundBody pExpand) ;; .set 0 (v 29)
def program : Program := LightReportingPositiveExpand.program ++ [body 49]
def time (h J k t n : ℕ) : ℕ := n*(LightReportingPositiveExpand.time h J k t+200)+100
def Inv {h J k : ℕ} (μ : ℕ → ℤ) (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J)
    (t baseL baseR boxCut indexBase ptrBase inL inR outL outR masks dstL dstR dst selected maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame (([width h J,h,rowMask (outputRows w.2.2) ⟨k,hk⟩,subsetMask (querySet k (outputRows w.2.2)),
      masks,dstL,dstR,work,sourceCut h J,suffixStage J (512*h) (k+1),(k+1)*h,residualSize h J (k+1),
      t,baseL,baseR,boxCut,indexBase,ptrBase,count h (k+1),groupSize h,dst,selected,maskBase,(k+1)*(512*h),
      inL,inR,pres.length,outL,outR,(through I w pres hk j).length,j] : List ℕ).map
      (fun n => (n : ℤ)) ++ [a,b,r]),ν⟩ ∧
    SegN ν outL ((through I w pres hk j).map fun pre => subsetMask (leftPrefix (k+1) (prefixRows (J := J) pre))) ∧
    SegN ν outR ((through I w pres hk j).map fun pre =>
      subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) pre))) ∧
    KeptOutputs μ ν masks outL outR (through I w pres hk j).length
end ThreeSum.LightReportingFrontierStep


