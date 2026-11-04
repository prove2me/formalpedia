-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
-- name    : Submission_ThreeSum_ReportingHostCatalogIndexCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:11:49.497233+00:00
-- url     : https://prove2.me/theorems/683077c9-a236-48ea-b7c1-545e41c71c58
-- title:
--   Reporting Host Catalog Index Costs
-- statement:
--   Definitions and structural lemmas for Reporting Host Catalog Index Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
set_option autoImplicit false
namespace ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000
end ThreeSum.ReportingHostCatalogIndexCosts


