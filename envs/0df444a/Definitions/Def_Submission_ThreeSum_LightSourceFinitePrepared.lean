-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceFinitePrepared
-- name    : Submission_ThreeSum_LightSourceFinitePrepared
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:54:46.034837+00:00
-- url     : https://prove2.me/theorems/691240ef-0a7a-44e8-bfd0-ee6f11b7dac7
-- title:
--   Light Source Finite Prepared
-- statement:
--   Definitions and structural lemmas for Light Source Finite Prepared, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceFinitePrepared.lean

import Definitions.Def_Submission_ThreeSum_SourceFiniteData
set_option autoImplicit false
namespace ThreeSum.LightSourceFinitePrepared
open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs
def args (free base bv be cv ce g p h J cut len : ℕ) : List ℤ :=
  [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,
    maps free h,candidates free h,leftCounts free h,rightCounts free h,
    bv,be,cv,ce,g,p,LightGuardedWanted.wantedFree free h J len+3,base,scheduleSize h]
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceFinitePrepared


