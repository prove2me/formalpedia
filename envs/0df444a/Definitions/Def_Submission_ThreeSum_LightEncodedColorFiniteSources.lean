-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorFiniteSources
-- name    : Submission_ThreeSum_LightEncodedColorFiniteSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:12:53.273901+00:00
-- url     : https://prove2.me/theorems/63514379-1d07-41a8-815b-3b86bcb6e22f
-- title:
--   Light Encoded Color Finite Sources
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Finite Sources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorFiniteSources.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorSourcesCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteRetention
set_option autoImplicit false
namespace ThreeSum.LightEncodedColorFiniteSources
open Light Scales TrimScales BandScales
def base (free n p M : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightEncodedColorSources.sourceBase free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) xs
def args (free bv be cv ce n p len : ℕ) : List ℤ :=
  [microHalf (inputBits n),blockCount (inputBits n),mu n,bv,be,cv,ce,bandSize n,p,
    LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) len,free]
variable {lim : Limits} {d : ℕ}
end ThreeSum.LightEncodedColorFiniteSources


