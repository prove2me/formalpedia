-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
-- name    : Submission_ThreeSum_LightBandRawAResourcesScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:29:08.611871+00:00
-- url     : https://prove2.me/theorems/28aff280-1222-4c98-be59-1ddc775fcad6
-- title:
--   Light Band Raw AResources Scales
-- statement:
--   Definitions and structural lemmas for Light Band Raw AResources Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResourcesScales.lean

import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
set_option autoImplicit false
namespace ThreeSum.LightBandRawAResources
open Light Scales BandScales StageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
def base (n : ℕ) : ℕ :=
  (SharedReportingBankResourceBounds.magnitude n + 1) * (n + 1) ^ 2
def envelope (n : ℕ) : ℕ :=
  1000 * base n
def need (n U : ℕ) : Light.Need :=
  ⟨LightBandRawAColor.word (inputBits n + 1) n (bandSize n) U, cells (inputBits n + 1) n (bandSize n),
    LightBandRawAColor.depth (inputBits n + 1) n (bandSize n)⟩
noncomputable section
end
end ThreeSum.LightBandRawAResources


