-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSwitchCosts
-- name    : Submission_ThreeSum_LightSwitchCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:24:30.434935+00:00
-- url     : https://prove2.me/theorems/e9477be5-9cf3-4a64-be45-408c1db2172f
-- title:
--   Light Switch Costs
-- statement:
--   Definitions and structural lemmas for Light Switch Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchCosts.lean

import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
set_option autoImplicit false
namespace ThreeSum.LightSwitchCosts
open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology
def timeBudget (n : ℕ) : ℕ := 100*(inputBits n+1)+50
def depthBudget (n : ℕ) : ℕ := 5200*inputBits n+90
def wordBudget (n : ℕ) : ℕ := (300*inputBits n+1001)^64
def allTimeBudget (n : ℕ) : ℕ :=
  depthBudget n+(20*inputBits n+1)*timeBudget n
noncomputable section
end
end ThreeSum.LightSwitchCosts


