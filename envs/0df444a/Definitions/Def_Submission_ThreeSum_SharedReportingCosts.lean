-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingCosts
-- name    : Submission_ThreeSum_SharedReportingCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:15:14.516336+00:00
-- url     : https://prove2.me/theorems/52b3bacd-edd3-4ce3-a150-9aa0618fb859
-- title:
--   Shared Reporting Costs
-- statement:
--   Definitions and structural lemmas for Shared Reporting Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingCosts.lean

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
namespace ThreeSum.SharedReportingCosts
open Scales CostLedger ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def localWidth (n : ℕ) : ℕ := 512*half n
def width (n : ℕ) : ℕ := blocks n*localWidth n
def localCount (n : ℕ) : ℕ := LightReportingPrefixArrays.localCount (localWidth n) (half n)
def overhead (n : ℕ) : ℕ :=
  100000*(width n+1)^5+5000*(localWidth n+1)^2*(localSearch 257 n+1)+
    1200*(blocks n+1)+2000*(width n+1)+1050
def time (n k : ℕ) : ℕ := LightReportingCatalogIndex.time (half n) (blocks n) k
  (Switch.residualSize n k-Switch.actualSwitch n k)
def levelsTime (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (Switch.terminalDepth n+1), time n k
def sharedTime (n : ℕ) : ℕ :=
  3*CostLedger.bandCount n^2*TrimScales.scheduleCount n*levelsTime n
def budget (n : ℕ) : ℕ := overhead n*StageBounds.boxCount n
end ThreeSum.SharedReportingCosts


