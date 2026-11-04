-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingGatherPair
-- name    : Submission_ThreeSum_LightReportingGatherPair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:13.538592+00:00
-- url     : https://prove2.me/theorems/32d7a138-d6fd-4b27-8f6c-d75f3ac7c32f
-- title:
--   Light Reporting Gather Pair
-- statement:
--   Definitions and structural lemmas for Light Reporting Gather Pair, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGatherPair.lean

import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightReportingGatherPair
open Light
variable {lim : Limits}
def body (pGather : ℕ) : Stmt :=
  .call pGather [v 0,v 1,v 5,v 3,v 4] 7 ;;
  .call pGather [v 0,v 2,v 6,v 3,v 4] 0
def program : Program := LightReportingGather.program ++ [body 0]
def time (t : ℕ) : ℕ := 2*LightReportingGather.time t+60
end ThreeSum.LightReportingGatherPair


