-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostCatalogSelection
-- name    : Submission_ThreeSum_ReportingHostCatalogSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:15:40.447776+00:00
-- url     : https://prove2.me/theorems/23c010ec-2b2e-4713-9ffc-ef18b58aeb16
-- title:
--   Reporting Host Catalog Selection
-- statement:
--   Definitions and structural lemmas for Reporting Host Catalog Selection, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogSelection.lean

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
set_option autoImplicit false
namespace ThreeSum.ReportingHostCatalogSelection
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
end ThreeSum.ReportingHostCatalogSelection


