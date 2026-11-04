-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingCatalogLevel
-- name    : Submission_ThreeSum_LightReportingCatalogLevel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:31:46.878194+00:00
-- url     : https://prove2.me/theorems/0f2b4b9c-a9a6-4fcd-a9f1-fee9f8469453
-- title:
--   Light Reporting Catalog Level
-- statement:
--   Definitions and structural lemmas for Light Reporting Catalog Level, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLevel.lean

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogBatch
import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightReportingCatalogLevel
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def body (pBatch pFilter : ℕ) : Stmt :=
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,
    v 16,v 17,v 18,v 19,v 20,v 21] 23 ;;
  .call pFilter [v 18,v 19,v 22] 0
def suffix : Program := [LightReportingFilter.body,body 36 37]
def program : Program := LightReportingCatalogBatch.program ++ suffix
def time (h J k t n : ℕ) : ℕ := LightReportingCatalogBatch.time h J k t n+LightReportingFilter.time n+100
end ThreeSum.LightReportingCatalogLevel


