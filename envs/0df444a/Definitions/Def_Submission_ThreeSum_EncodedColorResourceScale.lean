-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
-- name    : Submission_ThreeSum_EncodedColorResourceScale
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:33:40.631199+00:00
-- url     : https://prove2.me/theorems/5afea5b3-5123-4635-ad43-24e7b1159d8e
-- title:
--   Encoded Color Resource Scale
-- statement:
--   Definitions and structural lemmas for Encoded Color Resource Scale, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorResourceScale.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
set_option autoImplicit false
namespace ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def width (n : ℕ) : ℕ := blocks n*(512*half n)
def localEnvelope (n : ℕ) : ℕ := LightLocalCoverInitResources.envelope (half n)
def scale (n : ℕ) : ℕ := SharedReportingBankResourceBounds.magnitude n+localEnvelope n+
  maxMod n+primeWindow n+n+100
noncomputable section
end
end ThreeSum.EncodedColorResources


