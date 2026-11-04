-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSwitchScalar
-- name    : Submission_ThreeSum_LightSwitchScalar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:57.321702+00:00
-- url     : https://prove2.me/theorems/982598b4-22b9-4edd-a218-bcf69760c4ab
-- title:
--   Light Switch Scalar
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
set_option autoImplicit false
namespace ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000
def Small (B : ℕ) : Expr → Prop
  | .const n => n ≤ B
  | .var _ => True
  | .op _ a b => Small B a ∧ Small B b
  | .load _ => False
end ThreeSum.LightSwitchScalar


