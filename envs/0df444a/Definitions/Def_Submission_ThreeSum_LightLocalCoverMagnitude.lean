-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
-- name    : Submission_ThreeSum_LightLocalCoverMagnitude
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:11:21.977258+00:00
-- url     : https://prove2.me/theorems/c71ef1e7-22a6-48c0-9455-3971c23b637b
-- title:
--   Light Local Cover Magnitude
-- statement:
--   Definitions and structural lemmas for Light Local Cover Magnitude, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverMagnitude.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
set_option autoImplicit false
namespace ThreeSum.LightLocalCoverMagnitude
open LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
def magnitude (h : ℕ) : ℕ := 2^(600000*(h+1)^2)
structure Bounds (h B : ℕ) : Prop where
  positive : 1 ≤ B
  width : 512*h+1 ≤ B
  vertices : LightLocalCoverLayout.vertices h+1 ≤ B
  prime : localPrime h+1 ≤ B
  cap : localBucketCap h+1 ≤ B
  candidates : rows h+1 ≤ B
  rounds : scheduleSize h+1 ≤ B
  decodePower : (localPrime h)^(2*(512*h)+1)+1 ≤ B
  maskPower : 2^(512*h+1)+1 ≤ B
end ThreeSum.LightLocalCoverMagnitude


