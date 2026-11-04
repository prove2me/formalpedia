-- Prove2me | Definitions.Def_Submission_ThreeSum_MassScales
-- name    : Submission_ThreeSum_MassScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:07:57.980829+00:00
-- url     : https://prove2.me/theorems/f02ceeae-65db-4877-b5b1-77c2c58c7cd5
-- title:
--   Mass Scales
-- statement:
--   Definitions and structural lemmas for Mass Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean

import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
namespace ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def wantedNumerator (n : ℕ) : ℕ :=
  9 * scheduleCount n * typedOutputs n * bandCount n ^ 2 * bandSize n
def rawTripleBound (n : ℕ) : ℕ := 3 * bandCount n ^ 2 * bandSize n ^ 3
def falseNumerator (k n : ℕ) : ℕ :=
  candidateCount n * rawTripleBound n * scoreLoss k n * primeLoss radix n
noncomputable section
def wantedMajorant (n : ℕ) : ℝ := (wantedNumerator n : ℝ) / radix n
def falseMajorant (k n : ℕ) : ℝ := (falseNumerator k n : ℝ) / radix n
end
end ThreeSum.MassScales


