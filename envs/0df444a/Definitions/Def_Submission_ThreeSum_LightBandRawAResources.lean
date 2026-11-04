-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandRawAResources
-- name    : Submission_ThreeSum_LightBandRawAResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:54:08.662919+00:00
-- url     : https://prove2.me/theorems/6e62b075-42ee-4c74-8370-6735c59b320c
-- title:
--   Light Band Raw AResources
-- statement:
--   Definitions and structural lemmas for Light Band Raw AResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
set_option autoImplicit false
namespace ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
def cells (W n g : ℕ) : ℕ :=
  LightBandRawAColor.space (tables 0 n) (vals 0 n g) W n g
end ThreeSum.LightBandRawAResources


