-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:27:03.283594+00:00
-- url     : https://prove2.me/theorems/c11e3838-534c-400a-8251-18bd8350fcc3
-- title:
--   LightTernaryMomentReporter
-- statement:
--   Definitions and structural lemmas for LightTernaryMomentReporter, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentReporter.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDriverResources
import Definitions.Def_Submission_ThreeSum_LightTernaryPhysicalMomentBatch
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


