-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
-- name    : Submission_Weighted_Global_LightTernaryPostSelectionClosed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:09:00.047132+00:00
-- url     : https://prove2.me/theorems/9b556793-1beb-4330-8f20-7bb43408fff3
-- title:
--   Light Ternary Post Selection Closed
-- statement:
--   Definitions and structural lemmas for Light Ternary Post Selection Closed, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
namespace ThreeSum.LightWeightedGlobalCompactReporter
open Light TernaryMomentSchedule
def closedProgram (xl yl zl xr yr zr : List ℤ) (H : ℕ) : Program :=
  LightWeightedGlobalMomentReporter.closedProgram xl yl zl xr yr zr H++
    [body (139*(channels (2*H+1)).length+6)]
end ThreeSum.LightWeightedGlobalCompactReporter
namespace ThreeSum.LightWeightedGlobalPostSelection
open Light TernaryMomentSchedule
def closedProgram (xl yl zl xr yr zr : List ℤ) (H : ℕ) : Program :=
  ReportingHostRelocation.program LightOriginalSurvivorPair.program
    (LightWeightedGlobalCompactReporter.closedProgram xl yl zl xr yr zr H)++
      [body (9+(139*(channels (2*H+1)).length+7))]
end ThreeSum.LightWeightedGlobalPostSelection


