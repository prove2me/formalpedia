-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
-- name    : Submission_ThreeSum_LightColorParametersCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:23:52.966338+00:00
-- url     : https://prove2.me/theorems/4e58c445-df21-471f-98ea-ee8b80cab612
-- title:
--   Light Color Parameters Costs
-- statement:
--   Definitions and structural lemmas for Light Color Parameters Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorParametersCosts.lean

import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
set_option autoImplicit false
namespace ThreeSum.LightColorParametersCosts
open ColorParameters Scales StageBounds
def width (n : ℕ) : ℕ := inputBits n+1
def allTime (W : ℕ) : ℕ := count W*(100*count W+3000)+100
def timeBudget (n : ℕ) : ℕ := allTime (width n)
def wordBudget (n : ℕ) : ℕ := count (width n)+width n+10
open Filter Real
open scoped Topology
noncomputable section
end
end ThreeSum.LightColorParametersCosts


