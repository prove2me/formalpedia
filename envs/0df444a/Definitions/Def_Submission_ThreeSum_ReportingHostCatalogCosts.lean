-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
-- name    : Submission_ThreeSum_ReportingHostCatalogCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:42:32.269501+00:00
-- url     : https://prove2.me/theorems/1cc44995-c0ae-4112-b8dc-e4506e358435
-- title:
--   Reporting Host Catalog Costs
-- statement:
--   Definitions and structural lemmas for Reporting Host Catalog Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_CostLedger
set_option autoImplicit false
namespace ThreeSum.ReportingHostCatalogCosts
set_option maxRecDepth 8000
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts
end ThreeSum.ReportingHostCatalogCosts


