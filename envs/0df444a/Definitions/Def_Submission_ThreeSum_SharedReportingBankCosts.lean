-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
-- name    : Submission_ThreeSum_SharedReportingBankCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:01:05.599148+00:00
-- url     : https://prove2.me/theorems/4031fc47-9bbc-4546-afad-2e8e43dcb160
-- title:
--   Shared Reporting Bank Costs
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean

import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankCosts
open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
def roundExtra (n : ℕ) : ℕ :=
  LightSwitchCosts.timeBudget n+1400*(width n+1)^2+2808
def roundOverhead (n : ℕ) : ℕ := SharedReportingCosts.overhead n+roundExtra n
def setup (n : ℕ) : ℕ :=
  LightSwitchCosts.depthBudget n+1500*(localWidth n+1)^2+3300
def overhead (n : ℕ) : ℕ := roundOverhead n+1600+setup n
def budget (n : ℕ) : ℕ := overhead n*(boxCount n+1)
noncomputable section
end
end ThreeSum.SharedReportingBankCosts


