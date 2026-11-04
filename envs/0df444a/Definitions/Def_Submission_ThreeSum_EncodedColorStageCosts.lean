-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
-- name    : Submission_ThreeSum_EncodedColorStageCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:45:52.435545+00:00
-- url     : https://prove2.me/theorems/1e62b09e-9ad5-477c-a857-469de00878c3
-- title:
--   Encoded Color Stage Costs
-- statement:
--   Definitions and structural lemmas for Encoded Color Stage Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
set_option autoImplicit false
namespace ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
def incidenceCap (n : ℕ) : ℕ := bandSize n*ColorBandBounds.count n (bandSize n)
def sourceBase (free n M len : ℕ) : ℕ :=
  EncodedColorWantedCosts.sourceBase free M (microHalf (inputBits n)) (blockCount (inputBits n)) len
def time (n P M U len : ℕ) : ℕ :=
  EncodedColorWantedCosts.time P M (microHalf (inputBits n)) (blockCount (inputBits n)) U len+
    EncodedColorSourcesCosts.time n P U M+400
def space (free n P M U len : ℕ) : ℕ :=
  max (EncodedColorWantedCosts.space free P M (microHalf (inputBits n)) (blockCount (inputBits n)) U len)
    (SourceFiniteCosts.space (sourceBase free n M len) n P U M)
def word (n P M U len : ℕ) : ℕ :=
  LightEncodedColorWantedSources.word n P M U len
def depth (n M len : ℕ) : ℕ := LightEncodedColorWantedSources.depth n M len
end ThreeSum.EncodedColorStageCosts


