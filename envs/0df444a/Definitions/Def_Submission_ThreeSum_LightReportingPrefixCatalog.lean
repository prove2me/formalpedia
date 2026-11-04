-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
-- name    : Submission_ThreeSum_LightReportingPrefixCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:57:24.804884+00:00
-- url     : https://prove2.me/theorems/7b7e1645-9c90-48f0-88ef-aeee4a64aae7
-- title:
--   Light Reporting Prefix Catalog
-- statement:
--   Definitions and structural lemmas for Light Reporting Prefix Catalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean

import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingPrefixCatalog
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}
def count (h k : ℕ) : ℕ := (LightReportingPrefixArrays.localCount (512*h) h)^k
def body (pPrefixes pCatalog : ℕ) : Stmt :=
  .call pPrefixes [v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 19] 20 ;;
  .set 21 (M (v 20)) ;;
  .set 22 (v 20 -' v 14) ;;
  .set 23 (v 15 +' v 22) ;;
  .set 24 (v 20 +' k 1) ;;
  .set 25 (v 23 +' k 1) ;;
  .set 26 (v 10 *' v 9) ;;
  .call pCatalog [v 0,v 1,v 2,v 3,v 26,v 26,v 4,v 5,v 6,v 7,v 24,v 25,v 21,
    v 16,v 17,v 18,v 19] 27 ;;
  .set 0 (v 20)
def program : Program :=
  ReportingHostRelocation.program LightReportingPrefixArrays.program LightReportingSuffixCatalogSetup.program ++
    [body 10 42]
def time (h J k boxCut : ℕ) : ℕ :=
  LightReportingPrefixArrays.time (512*h) h k+
    LightReportingSuffixCatalogSetup.time (J*(512*h)) ((J-k)*(512*h)) boxCut (k*(512*h)) (count h k)+500
end ThreeSum.LightReportingPrefixCatalog


