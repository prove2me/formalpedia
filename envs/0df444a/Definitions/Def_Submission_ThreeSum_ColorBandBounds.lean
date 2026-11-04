-- Prove2me | Definitions.Def_Submission_ThreeSum_ColorBandBounds
-- name    : Submission_ThreeSum_ColorBandBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:37.580205+00:00
-- url     : https://prove2.me/theorems/017859ec-a4aa-45e7-967f-abbc76e1527f
-- title:
--   Color Band Bounds
-- statement:
--   Definitions and structural lemmas for Color Band Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorBandBounds.lean

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
set_option autoImplicit false
namespace ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
def count (n g : ℕ) : ℕ := 3*(size n g)^2
def width (n g : ℕ) : ℕ := LightBandEnumeration.width (size n g) (size n g) (size n g)
def time (n g : ℕ) : ℕ :=
  2100*(n+1)*(Nat.clog 2 n+1)+1000*(count n g+n+1)*(width n g+1)+400
def space (work n g : ℕ) : ℕ := work+n+count n g+width n g+1
def word (n g U : ℕ) : ℕ := n+g+2+
  LightBandEnumeration.word (size n g) (size n g) (size n g) U
def depth (n g : ℕ) : ℕ := n+Nat.clog 2 n+width n g+10
end ThreeSum.ColorBandBounds


