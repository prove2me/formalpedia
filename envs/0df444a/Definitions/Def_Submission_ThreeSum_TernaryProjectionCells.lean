-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryProjectionCells
-- name    : Submission_ThreeSum_TernaryProjectionCells
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:55:08.761118+00:00
-- url     : https://prove2.me/theorems/c330fb7d-36c2-468a-b33e-9ca3ec17e7b1
-- title:
--   Ternary Projection Cells
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProjectionCells.lean

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace ThreeSum.TernaryProjectionCells
variable {K : Type*} [Field K]
def projectedCell (a b : K) : Fin 6 → K := ![0,b,a,2*b,a+b,2*a]
end ThreeSum.TernaryProjectionCells


