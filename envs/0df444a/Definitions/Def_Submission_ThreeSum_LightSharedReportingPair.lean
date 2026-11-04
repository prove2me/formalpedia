-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSharedReportingPair
-- name    : Submission_ThreeSum_LightSharedReportingPair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:29:25.217166+00:00
-- url     : https://prove2.me/theorems/9a10f06c-ac7c-4357-80ee-8f1f30d5c78b
-- title:
--   Light Shared Reporting Pair
-- statement:
--   Definitions and structural lemmas for Light Shared Reporting Pair, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingPair.lean

import Definitions.Def_Submission_ThreeSum_LightSharedReportingLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSharedReportingPair
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankLayout SharedReportingBankLevels SharedReportingBankSources
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
def body (pLevels : ℕ) : Stmt :=
  .set 12 (v 3 +' v 6 *' v 4 +' k 2 *' v 5) ;;
  .set 13 (v 3 +' v 7 *' v 4 +' k 2 *' v 5 +' k 1) ;;
  .call pLevels [v 0,v 1,v 2,v 12,v 13,v 8,v 9,v 10,v 11] 14 ;;
  .set 0 (v 14)
def time (h J K : ℕ) : ℕ := LightSharedReportingLevels.time h J K+500
def program : Program := LightSharedReportingLevels.program ++ [body 64]
end ThreeSum.LightSharedReportingPair


