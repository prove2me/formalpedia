-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingCatalogExpand
-- name    : Submission_ThreeSum_LightReportingCatalogExpand
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:34:57.934031+00:00
-- url     : https://prove2.me/theorems/4ee5d11a-b779-4e19-bd72-958faef59127
-- title:
--   Light Reporting Catalog Expand
-- statement:
--   Definitions and structural lemmas for Light Reporting Catalog Expand, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogExpand.lean

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLevel
import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightReportingCatalogExpand
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def body (pChildren pLevel : ℕ) : Stmt :=
  .call pChildren [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9] 26 ;;
  .call pLevel [v 0,v 10,v 11,v 12,v 12,v 11,v 25,v 13,v 26,v 14,v 15,v 16,v 17,
    v 18,v 19,v 20,v 7,v 8,v 21,v 22,v 24,v 9,v 23] 0
def program : Program :=
  ReportingHostRelocation.program LightBlockChildren.program LightReportingCatalogLevel.program ++
    [body 0 45]
def time (h J k t : ℕ) : ℕ :=
  LightBlockChildren.time (width h J) (2*h) h+
    LightReportingCatalogLevel.time h J (k+1) t (groupSize h)+150
end ThreeSum.LightReportingCatalogExpand


