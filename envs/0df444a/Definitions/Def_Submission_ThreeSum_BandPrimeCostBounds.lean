-- Prove2me | Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
-- name    : Submission_ThreeSum_BandPrimeCostBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:52:23.762992+00:00
-- url     : https://prove2.me/theorems/0bbb3f45-9e2d-47e1-9268-2bfe2365fe67
-- title:
--   Band Prime Cost Bounds
-- statement:
--   Definitions and structural lemmas for Band Prime Cost Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCostBounds.lean

import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
set_option autoImplicit false
namespace ThreeSum.BandPrimeCosts
open Filter Real Scales BandScales CostLedger Parameters StageBounds HierarchyScales
  ArithmeticStageBounds
open scoped Topology
set_option maxHeartbeats 1400000
noncomputable section
end
end ThreeSum.BandPrimeCosts


