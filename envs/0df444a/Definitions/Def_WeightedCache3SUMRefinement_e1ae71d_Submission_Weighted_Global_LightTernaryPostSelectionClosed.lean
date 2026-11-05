-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelectionClosed
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelectionClosed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:48:49.756037+00:00
-- url     : https://prove2.me/theorems/31029f87-ace9-4035-bf38-b0862e0c3dc2
-- title:
--   LightTernaryPostSelectionClosed
-- statement:
--   Definitions and structural lemmas for LightTernaryPostSelectionClosed, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelection
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


