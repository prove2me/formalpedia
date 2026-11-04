-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSharedReportingCounts
-- name    : Submission_ThreeSum_LightSharedReportingCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:06:16.302144+00:00
-- url     : https://prove2.me/theorems/64e0dc79-c7c5-4c69-b574-52f8546c5ca1
-- title:
--   Light Shared Reporting Counts
-- statement:
--   Definitions and structural lemmas for Light Shared Reporting Counts, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingCounts.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSharedReportingCounts
open Light LightPascal LightSubsetAddress SubsetAddress SharedReportingBankLayout
set_option maxHeartbeats 1700000
set_option maxRecDepth 9000
def body (pBuild : ℕ) : Stmt :=
  .set 3 (k 512 *' v 0) ;;
  .call pBuild [v 2,v 3] 4 ;;
  .set 5 (M (v 2 +' v 3 *' (v 3 +' k 1) +' v 0)) ;;
  .set 6 (M (v 2 +' v 3 *' (v 3 +' k 1) +' k 2 *' v 0)) ;;
  .set 7 (M (v 2 +' k 2 *' v 0 *' (v 3 +' k 1) +' v 0)) ;;
  .set 8 (v 6 *' v 7) ;;
  .store (v 1) (v 5) ;;
  .store (v 1 +' k 1) (v 8) ;;
  .set 0 (v 8)
def program : Program := [body 1,buildBody 2 3,fillBody,rowBody 4,LightArray.linearBody]
def time (h : ℕ) : ℕ := buildTime (512*h)+300
end ThreeSum.LightSharedReportingCounts


