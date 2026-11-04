-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
-- name    : Submission_Weighted_Global_LightTernaryMomentReporter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:09:30.613373+00:00
-- url     : https://prove2.me/theorems/0fcb879d-a775-4a73-8994-cb9c23cb85ae
-- title:
--   Light Ternary Moment Reporter
-- statement:
--   Definitions and structural lemmas for Light Ternary Moment Reporter, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentReporter.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDriverResources
import Definitions.Def_Submission_ThreeSum_LightTernaryPhysicalMomentBatch
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalMomentReporter
open Light TernaryMomentSchedule
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000
def driver {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  LightWeightedGlobalCertifiedMomentDriver.program S (2*H+1)
def body (pDriver pDetector : ℕ) : Stmt :=
  .call pDriver (LightWeightedSourceCountHost.callArgs 6 115) 121 ;;
  .call pDetector [v 3,v 5,v 0,v 1,v 4,v 2] 0
def libraries {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  ReportingHostRelocation.program (driver S H) (LightTernaryMomentBatch.program H)
def program {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  libraries S H++[body (139*(channels (2*H+1)).length+1) (driver S H).length]
def closedProgram (xl yl zl xr yr zr : List ℤ) (H : ℕ) : Program :=
  let base := LightWeightedGlobalMomentDriver.program xl yl zl xr yr zr
    (channels (2*H+1)) (2*H+1) 115
  ReportingHostRelocation.program base (LightTernaryMomentBatch.program H)++
    [body (139*(channels (2*H+1)).length+1) (139*(channels (2*H+1)).length+2)]
def args {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (originalA originalCount scratch originalB originalC matrix : ℕ) : List ℤ :=
  [(originalA : ℤ),originalCount,scratch,S.front.records,matrix,S.front.count]++
    LightWeightedGlobalMomentChannelFactory.args S originalB originalC matrix
def time {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : ℕ :=
  LightWeightedGlobalCertifiedMomentDriver.time S (2*H+1)+LightTernaryMomentBatch.time H S.front.count+200
end ThreeSum.LightWeightedGlobalMomentReporter


