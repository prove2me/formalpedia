-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
-- name    : Submission_ThreeSum_LightBlockSourceBuild
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:57.12817+00:00
-- url     : https://prove2.me/theorems/28528b49-e536-48bd-a30c-9a4257011b80
-- title:
--   Light Block Source Build
-- statement:
--   Definitions and structural lemmas for Light Block Source Build, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
set_option autoImplicit false
namespace ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000
def endpointBound (h J : ℕ) : ℕ := J*(512*h)*(localPrime h^J*localPrime h)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightBlockSourceBuild


