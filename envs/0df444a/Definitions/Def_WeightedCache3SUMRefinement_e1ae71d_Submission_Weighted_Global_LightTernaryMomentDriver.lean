-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentDriver
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentDriver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:13:19.143798+00:00
-- url     : https://prove2.me/theorems/80f6c20b-b6a9-4eb2-b58b-7b8cd68d10f9
-- title:
--   LightTernaryMomentDriver
-- statement:
--   Definitions and structural lemmas for LightTernaryMomentDriver, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentDriver.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentSourceProgram
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_library

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalMomentDriver
open Light TernaryMomentSchedule
set_option maxHeartbeats 2000000
def library (xl yl zl xr yr zr : List ℤ) : List (ℕ×ℕ)→Program
  | [] => []
  | c::cs => ReportingHostRelocation.program
      (LightWeightedGlobalMomentSourceProgram.program xl yl zl xr yr zr c.1 c.2)
      (library xl yl zl xr yr zr cs)
def labels (steps : List (ℕ×ℕ)) : List (ℕ×ℕ) :=
  (List.range steps.length).map (fun i => (i,0))
def entry (c : ℕ×ℕ) : ℕ :=139*c.1+138
def body (steps : List (ℕ×ℕ)) (terms arity : ℕ) : Stmt :=
  .call (139*steps.length) [v 6,k terms *' v 7,k 0] arity ;;
  LightTernaryFixedChannelLoop.body (labels steps) entry arity
def program (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ)) (terms arity : ℕ) : Program :=
  library xl yl zl xr yr zr steps++[fillBody,body steps terms arity]
def time (steps : List (ℕ×ℕ)) (cost : (ℕ×ℕ)→ℕ) (terms count arity : ℕ) : ℕ :=
  fillTime (terms*count)+
    LightTernaryFixedChannelLoop.time (labels steps)
      (fun c => cost (steps.getD c.1 (0,0))) arity+100
variable {lim : Limits} {d : ℕ}
end ThreeSum.LightWeightedGlobalMomentDriver
end
end WeightedCache3SUMRefinement_e1ae71d


