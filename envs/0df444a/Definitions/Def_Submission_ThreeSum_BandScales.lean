-- Prove2me | Definitions.Def_Submission_ThreeSum_BandScales
-- name    : Submission_ThreeSum_BandScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:54:53.09756+00:00
-- url     : https://prove2.me/theorems/aa732546-173e-4883-aca8-ef0caccc79e7
-- title:
--   Band Scales
-- statement:
--   Definitions and structural lemmas for Band Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean

import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
namespace ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
def bandRoot (n : ℕ) : ℕ := LocalCoverBounds.rootCeiling (typedOutputs n)
def bandDivisor (n : ℕ) : ℕ := 2 ^ (mu n / 20)
def bandSize (n : ℕ) : ℕ := bandRoot n ⌈/⌉ bandDivisor n
noncomputable section
def unroundedBand (n : ℕ) : ℝ := (bandRoot n : ℝ) / bandDivisor n
end
end ThreeSum.BandScales


