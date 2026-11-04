-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
-- name    : Submission_ThreeSum_EncodedColorPrimeResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:40:25.629611+00:00
-- url     : https://prove2.me/theorems/b915e693-9320-4885-ae70-5a9c88d5fe46
-- title:
--   Encoded Color Prime Resources
-- statement:
--   Definitions and structural lemmas for Encoded Color Prime Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
set_option autoImplicit false
namespace ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
end ThreeSum.EncodedColorResources


