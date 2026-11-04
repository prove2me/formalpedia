-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
-- name    : Submission_ThreeSum_LightReportingCatalogQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:19:21.70698+00:00
-- url     : https://prove2.me/theorems/9087628d-e43d-4251-9d0f-a01c51bc078b
-- title:
--   Light Reporting Catalog Query
-- statement:
--   Definitions and structural lemmas for Light Reporting Catalog Query, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogQuery.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogSelection
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingCatalogQuery
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostCatalogSelection
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def body (pLookup pQuery : ℕ) : Stmt :=
  .call pLookup [v 0,v 17,v 15,v 4,v 6,v 19] 20 ;;
  .set 21 (M (v 16 +' v 20)) ;;
  .call pQuery [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 21,v 18,v 19] 0
def program : Program :=
  ReportingHostRelocation.program LightReportingCatalogLookup.program LightReportingSuffixQueryHost.program ++
    [body 3 34]
def time (h J k t : ℕ) : ℕ :=
  LightReportingCatalogLookup.time (width h J) (count h k)+
    LightReportingSuffixQueryHost.time (width h J) (suffixStage J (512*h) k) (residualSize h J k) t+100
end ThreeSum.LightReportingCatalogQuery


