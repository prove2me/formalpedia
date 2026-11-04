-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryQuarticStep
-- name    : Submission_Weighted_Global_LightTernaryQuarticStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:52:11.945092+00:00
-- url     : https://prove2.me/theorems/341d78ae-cda6-472e-b81d-e566c37fa47c
-- title:
--   Light Ternary Quartic Step
-- statement:
--   Definitions and structural lemmas for Light Ternary Quartic Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryQuarticStep.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorHeader
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightWeightedGlobalQuarticStep
open Light
set_option maxHeartbeats 2400000
def body (pChannel pCount pScatter : ℕ) : Stmt :=
  .call pChannel [v 1,v 2,v 5,v 11,v 12,v 6] 17 ;;
  .call pChannel [v 3,v 4,v 5,v 13,v 14,v 7] 18 ;;
  .call pCount LightWeightedGlobalTensorDriver.countArgs 19 ;;
  .call pScatter [v 10,v 8,v 9,v 16,v 15] 0
end ThreeSum.LightWeightedGlobalQuarticStep


