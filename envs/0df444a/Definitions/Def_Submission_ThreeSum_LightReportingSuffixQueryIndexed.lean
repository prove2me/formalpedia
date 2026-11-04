-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
-- name    : Submission_ThreeSum_LightReportingSuffixQueryIndexed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:36:08.940673+00:00
-- url     : https://prove2.me/theorems/667c053c-49d3-4f65-8fa9-6bbe15f14fa6
-- title:
--   Light Reporting Suffix Query Indexed
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Query Indexed, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixQueryIndexed.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryHost
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixQueryIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
end ThreeSum.LightReportingSuffixQueryIndexed


