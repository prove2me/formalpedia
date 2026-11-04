-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
-- name    : Submission_ThreeSum_LightReportingSuffixCatalogSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:38:01.590697+00:00
-- url     : https://prove2.me/theorems/e33afe48-440d-4513-ad09-26b40b1f422f
-- title:
--   Light Reporting Suffix Catalog Setup
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Catalog Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixCatalogSetup.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalog
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixCatalogSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix LightReportingSuffixCatalog
variable {lim : Limits}
def body (pSize pCatalog : ℕ) : Stmt :=
  .call pSize [v 6,v 2,v 16] 17 ;;
  .set 18 ((v 6 +' k 1) *' v 17) ;;
  .call pCatalog [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    v 13,v 14,v 18,v 15,v 16] 0
def program : Program := LightReportingSuffixCatalog.program ++ [body 9 30]
def time (W V cut offset n : ℕ) : ℕ :=
  LightDownsetSize.time V+LightReportingSuffixCatalog.time W V cut offset n+100
end ThreeSum.LightReportingSuffixCatalogSetup


