-- Prove2me | Definitions.Def_Submission_ThreeSum_HierarchyScales
-- name    : Submission_ThreeSum_HierarchyScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:04:17.953639+00:00
-- url     : https://prove2.me/theorems/4a04e3b8-f673-4749-bf52-d67ea3c2db07
-- title:
--   Hierarchy Scales
-- statement:
--   Definitions and structural lemmas for Hierarchy Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean

import Definitions.Def_Submission_ThreeSum_CostLedger
set_option autoImplicit false
namespace ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def initialCap (r : ℕ) : ℕ := r ⌈/⌉ 25
def polynomialFactor (C n : ℕ) : ℕ := (mu n + 1) ^ C
noncomputable section
def hierarchyEnvelope (C B : ℝ) (n : ℕ) : ℝ :=
  (mu n + 1 : ℝ) * Real.exp ((mu n : ℝ) * Real.log 2 * C + B)
def unroundedBandCount (n : ℕ) : ℝ := (n : ℝ) / BandScales.bandSize n
end
end ThreeSum.HierarchyScales


