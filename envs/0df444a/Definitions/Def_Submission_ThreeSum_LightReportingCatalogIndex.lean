-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
-- name    : Submission_ThreeSum_LightReportingCatalogIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:11:39.014206+00:00
-- url     : https://prove2.me/theorems/5106d599-6cb8-4147-aff4-68ea0026c18d
-- title:
--   Light Reporting Catalog Index
-- statement:
--   Definitions and structural lemmas for Light Reporting Catalog Index, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogIndex.lean

import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingCatalogIndex
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixOrder ReportingHostSuffix LightReportingSuffixCatalog
open LightReportingPrefixCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : Limits}
def body (pCatalog pIndex : ℕ) : Stmt :=
  .call pCatalog [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,
    v 14,v 15,v 16,v 17,v 18,v 19] 21 ;;
  .set 22 (M (v 21)) ;;
  .set 23 (v 21 -' v 14) ;;
  .set 24 (v 15 +' v 23 +' k 1) ;;
  .set 25 (v 21 +' k 1) ;;
  .call pIndex [v 0,v 25,v 24,v 22,v 20,v 19] 26 ;;
  .set 0 (v 21)
def program : Program :=
  ReportingHostRelocation.program LightReportingPrefixCatalog.program LightReportingSortedCatalog.program ++
    [body 43 50]
def time (h J k boxCut : ℕ) : ℕ := LightReportingPrefixCatalog.time h J k boxCut+
  LightReportingSortedCatalog.time (J*(512*h)) (count h k)+250
end ThreeSum.LightReportingCatalogIndex


