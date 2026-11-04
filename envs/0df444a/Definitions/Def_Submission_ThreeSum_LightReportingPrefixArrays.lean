-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
-- name    : Submission_ThreeSum_LightReportingPrefixArrays
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:50:28.070673+00:00
-- url     : https://prove2.me/theorems/3228297d-aaeb-4faf-bfa3-ed9d311f8fb2
-- title:
--   Light Reporting Prefix Arrays
-- statement:
--   Definitions and structural lemmas for Light Reporting Prefix Arrays, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixArrays.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingPrefixArrays
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration ReportingHostPairSegments
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : Limits}
def localCount (L h : ℕ) : ℕ := L.choose (2*h)*(2*h).choose h
def body (pPairs pPowers pKeys : ℕ) : Stmt :=
  .call pPairs [v 0,v 1,v 3,v 4,v 5,v 8] 9 ;;
  .call pPowers [v 8,v 0 +' k 1,k 2] 10 ;;
  .set 11 (M (v 8 +' v 0)) ;;
  .call pKeys [v 4,v 9,v 2,v 11,v 6] 12 ;;
  .call pKeys [v 5,v 9,v 2,v 11,v 7] 13 ;;
  .set 0 (v 12)
def program : Program := LightReportingPairRows.program ++
  [LightRadixKeys.body 8 9,LightRadixRows.body 6,body 7 2 8]
def time (L h k : ℕ) : ℕ :=
  LightReportingPairRows.time L h+powTableTime (L+1)+2*LightRadixKeys.time (localCount L h) k+250
end ThreeSum.LightReportingPrefixArrays


