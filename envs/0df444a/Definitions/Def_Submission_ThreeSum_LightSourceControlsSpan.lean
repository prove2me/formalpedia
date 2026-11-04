-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceControlsSpan
-- name    : Submission_ThreeSum_LightSourceControlsSpan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:28:38.709203+00:00
-- url     : https://prove2.me/theorems/908983a8-bd7f-4ce3-ab2b-14b712103c41
-- title:
--   Light Source Controls Span
-- statement:
--   Definitions and structural lemmas for Light Source Controls Span, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceControlsSpan.lean

import Definitions.Def_Submission_ThreeSum_SourceControlLayout
import Definitions.Def_Submission_ThreeSum_LightSourceControlsMax
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSourceControlsSpan
open Light SourceControlLayout
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000
def body (pMax : ℕ) : Stmt :=
  .set 6 (v 1 +' k 1) ;;
  .set 7 (v 6 *' v 6 +' v 6) ;;
  .call pMax [v 7,v 5 +' k 2] 8 ;;
  .call pMax [v 8,v 4 +' k 5] 9 ;;
  .call pMax [v 9,v 0 +' k 1] 10 ;;
  .set 11 (k 5 *' v 2 +' k 2 *' v 1 +' k 4 +' k 2 *' v 6 *' v 2) ;;
  .set 0 (v 3 *' v 11 +' v 2 +' v 1 +' k 2 +' v 10)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightSourceControlsMax.body]
end ThreeSum.LightSourceControlsSpan


