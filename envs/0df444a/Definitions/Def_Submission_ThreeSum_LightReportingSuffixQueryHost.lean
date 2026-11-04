-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryHost
-- name    : Submission_ThreeSum_LightReportingSuffixQueryHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:33:47.076018+00:00
-- url     : https://prove2.me/theorems/572fa01b-20a1-4cad-b683-2e4b10fa8608
-- title:
--   Light Reporting Suffix Query Host
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Query Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixQueryHost.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQuery
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixLower
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixQueryHost
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}
def body (pLower pQuery : ℕ) : Stmt :=
  .call pLower [v 0,v 7,v 8,v 10,v 17] 18 ;;
  .set 19 (M (v 17 +' v 8)) ;;
  .call pQuery [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 19,v 9,v 18,v 11,v 12,v 13,v 14,v 15,v 16,v 17] 0
def suffix : Program := [LightReportingSuffixLower.body 17 20,body 29 28]
def program : Program := LightReportingSuffixQuery.program ++ suffix
def time (W V c t : ℕ) : ℕ := LightReportingSuffixLower.time W V+LightReportingSuffixQuery.time W V c t+100
end ThreeSum.LightReportingSuffixQueryHost


