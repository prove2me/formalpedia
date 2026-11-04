-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSharedReportingCell
-- name    : Submission_ThreeSum_LightSharedReportingCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:06:44.123004+00:00
-- url     : https://prove2.me/theorems/a460c332-c1d6-40eb-8622-bc4619848960
-- title:
--   Light Shared Reporting Cell
-- statement:
--   Definitions and structural lemmas for Light Shared Reporting Cell, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingCell.lean

import Definitions.Def_Submission_ThreeSum_LightSharedReportingEntry
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSharedReportingCell
open Light SubsetAddress LightPascal ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog SharedReportingBankData
open SharedReportingBankLayout
set_option maxHeartbeats 2900000
set_option maxRecDepth 15000
def body (pSize pEntry : ℕ) : Stmt :=
  .set 13 (k 512 *' v 0) ;;
  .set 14 (v 1 *' v 13) ;;
  .set 15 ((v 1 -' v 2) *' v 13) ;;
  .call pSize [v 15,v 6,v 12] 16 ;;
  .set 17 (v 12 +' v 7) ;;
  .set 18 (v 17 +' v 8) ;;
  .set 19 (v 18 +' v 8) ;;
  .set 20 (v 19 +' v 10) ;;
  .set 21 (v 20 +' v 10) ;;
  .set 22 (v 21 +' v 9) ;;
  .set 23 ((v 15 +' k 1) *' v 16) ;;
  .set 24 (v 22 +' v 9 *' v 23) ;;
  .set 25 (v 24 +' v 16 +' v 9) ;;
  .set 26 (v 25 +' k 2 *' v 13 +' k 2 +' k 1 +'
    (v 14 +' k 1) *' (v 14 +' k 1) +' (v 14 +' k 1) +' v 9) ;;
  .set 27 (k 2 *' v 0 *' v 1) ;;
  .call pEntry [v 14,v 27,v 6,v 15,v 15,v 2 *' v 13,v 3,v 4,v 13,v 0,v 2,
    v 12,v 17,v 18,v 19,v 20,v 21,v 22,v 24,v 25,v 24,v 5,v 11] 28 ;;
  .set 0 (v 26)
def program : Program :=
  ReportingHostRelocation.program LightSharedReportingEntry.program LightDownsetSize.program ++
    [body 53 52]
def time (h J k boxCut : ℕ) : ℕ :=
  LightDownsetSize.time ((J-k)*(512*h))+LightSharedReportingEntry.time h J k boxCut+1500
end ThreeSum.LightSharedReportingCell


