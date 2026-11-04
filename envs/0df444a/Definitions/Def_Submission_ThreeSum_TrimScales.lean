-- Prove2me | Definitions.Def_Submission_ThreeSum_TrimScales
-- name    : Submission_ThreeSum_TrimScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:53:45.253952+00:00
-- url     : https://prove2.me/theorems/9ab90a7d-8be4-4137-8269-0e1f89c1ac28
-- title:
--   Trim Scales
-- statement:
--   Definitions and structural lemmas for Trim Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
set_option autoImplicit false
namespace ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
def replicatedHalf (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  f (microHalf (inputBits n)) ^ blockCount (inputBits n)
def typedVertices (n : ℕ) : ℕ :=
  replicatedHalf (fun h => LocalCoverBounds.vertexCount (512 * h) h) n
def trimMultiplicity (n : ℕ) : ℕ :=
  LocalCoverBounds.localBucketCap (microHalf (inputBits n)) ^ (2 * blockCount (inputBits n))
def localLength (h : ℕ) : ℕ := (LocalHashMoments.localSchedule h).length
def scheduleCount (n : ℕ) : ℕ := replicatedHalf localLength n
def representationBound (n : ℕ) : ℕ :=
  (localLength (microHalf (inputBits n)) *
    LocalCoverBounds.localBucketCap (microHalf (inputBits n)) ^ 2) ^ blockCount (inputBits n)
def fullOutputs (n : ℕ) : ℕ := (256 * mu n).choose (mu n)
def representationDomain (n : ℕ) : ℕ := 2 ^ mu n
noncomputable section
def vertexLoad (h : ℕ) : ℝ :=
  (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h
end
end ThreeSum.TrimScales


