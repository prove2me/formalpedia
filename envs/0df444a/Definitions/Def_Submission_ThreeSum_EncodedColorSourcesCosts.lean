-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorSourcesCosts
-- name    : Submission_ThreeSum_EncodedColorSourcesCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:06:07.732078+00:00
-- url     : https://prove2.me/theorems/58912e67-c5ae-4a9b-87c8-13b7c76cb8d0
-- title:
--   Encoded Color Sources Costs
-- statement:
--   Definitions and structural lemmas for Encoded Color Sources Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourcesCosts.lean

import Definitions.Def_Submission_ThreeSum_LightEncodedColorSources
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
set_option autoImplicit false
namespace ThreeSum.EncodedColorSourcesCosts
open Scales TrimScales BandScales
def time (n p U M : ℕ) : ℕ :=
  LightNatPower.time (blockCount (inputBits n))+SourceFiniteCosts.time n p U M+1000
end ThreeSum.EncodedColorSourcesCosts


