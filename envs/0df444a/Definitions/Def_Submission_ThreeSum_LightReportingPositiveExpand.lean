-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingPositiveExpand
-- name    : Submission_ThreeSum_LightReportingPositiveExpand
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:47:45.578318+00:00
-- url     : https://prove2.me/theorems/fdc6bd92-5cb5-464a-b87d-d3d871eed071
-- title:
--   Light Reporting Positive Expand
-- statement:
--   Definitions and structural lemmas for Light Reporting Positive Expand, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveExpand.lean

import Definitions.Def_Submission_ThreeSum_LightReportingPositiveMasks
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingPositiveExpand
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive LightReportingPositiveMasks
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def body (pExpand pGather : ℕ) : Stmt :=
  .call pExpand [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,
    v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25] 28 ;;
  .call pGather [v 23,v 7,v 8,v 28,v 21,v 26,v 27] 29 ;;
  .set 0 (v 28)
def program : Program :=
  ReportingHostRelocation.program LightReportingCatalogExpand.program LightReportingGatherPair.program ++
    [body 46 48]
def time (h J k t : ℕ) : ℕ :=
  LightReportingCatalogExpand.time h J k t+LightReportingGatherPair.time (groupSize h)+120
abbrev KeptOutputs (μ ν : ℕ → ℤ) (bound outL outR n : ℕ) : Prop :=
  SameOn (fun i => i < bound ∧ Outside outL n i ∧ Outside outR n i) μ ν
end ThreeSum.LightReportingPositiveExpand


