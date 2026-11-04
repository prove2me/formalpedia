-- Prove2me | Definitions.Def_Submission_ThreeSum_UniformStageBounds
-- name    : Submission_ThreeSum_UniformStageBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:14:54.444456+00:00
-- url     : https://prove2.me/theorems/4f7de877-d73c-402f-bf8d-699d878ce846
-- title:
--   Uniform Stage Bounds
-- statement:
--   Definitions and structural lemmas for Uniform Stage Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean

import Definitions.Def_Submission_ThreeSum_StageBounds
set_option autoImplicit false
namespace ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def wantedBudget (n : ℕ) : ℕ := wantedNumerator n / radix n
def falseBudget (k n : ℕ) : ℕ := falseNumerator k n / radix n
def workBudget (C k n : ℕ) : ℕ := amplifiedCoreWork C wantedBudget (falseBudget k) n
noncomputable section
end
end ThreeSum.UniformStageBounds


