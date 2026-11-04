-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSharedReportingEntry
-- name    : Submission_ThreeSum_LightSharedReportingEntry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:02:19.129585+00:00
-- url     : https://prove2.me/theorems/4a89afad-6c30-4938-83e8-06b7034d69d4
-- title:
--   Light Shared Reporting Entry
-- statement:
--   Definitions and structural lemmas for Light Shared Reporting Entry, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingEntry.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSharedReportingEntry
open Light SubsetAddress LightPascal ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
open SharedReportingBankData
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
def body (pCatalog : ℕ) : Stmt :=
  .set 23 (M (v 6)) ;;
  .set 24 (M (v 7)) ;;
  .call pCatalog [v 0,v 1,v 2,v 3,v 4,v 5,v 23,v 24,v 8,v 9,v 10,v 11,
    v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20] 25 ;;
  .set 26 (M (v 25)) ;;
  .store (v 22) (v 21) ;;
  .store (v 22 +' k 1) (v 2) ;;
  .store (v 22 +' k 2) (v 20) ;;
  .store (v 22 +' k 3) (v 16) ;;
  .store (v 22 +' k 4) (v 26) ;;
  .set 0 (v 26)
def program : Program := LightReportingCatalogIndex.program ++ [body 51]
def time (h J k boxCut : ℕ) : ℕ := LightReportingCatalogIndex.time h J k boxCut+500
end ThreeSum.LightSharedReportingEntry


