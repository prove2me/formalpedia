-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
-- name    : Submission_ThreeSum_SharedReportingCostBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:19:25.476176+00:00
-- url     : https://prove2.me/theorems/5226933b-b02b-43f5-af49-ed6da671b17e
-- title:
--   Shared Reporting Cost Bounds
-- statement:
--   Definitions and structural lemmas for Shared Reporting Cost Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingCostBounds.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
set_option autoImplicit false
namespace ThreeSum.SharedReportingCosts
open Filter Real Scales Parameters StageBounds ArithmeticStageBounds
open scoped Topology
set_option maxHeartbeats 1500000
noncomputable section
end
end ThreeSum.SharedReportingCosts


