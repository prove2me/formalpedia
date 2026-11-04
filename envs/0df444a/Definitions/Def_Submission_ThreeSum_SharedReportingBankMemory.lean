-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
-- name    : Submission_ThreeSum_SharedReportingBankMemory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:07:01.514222+00:00
-- url     : https://prove2.me/theorems/37eb1390-5c58-4908-8e83-5e0a9a31ab0b
-- title:
--   Shared Reporting Bank Memory
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Memory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankMemory.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
end ThreeSum.SharedReportingBankData


