-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
-- name    : Submission_ThreeSum_SourceBandPairSlices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:59:43.567045+00:00
-- url     : https://prove2.me/theorems/6ae14ea7-2692-4a89-b701-3274c0b57c94
-- title:
--   Source Band Pair Slices
-- statement:
--   Definitions and structural lemmas for Source Band Pair Slices, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairSlices.lean

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
set_option autoImplicit false
namespace ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData
def histogramPtr (base n g m zero i : ℕ) : ℕ :=
  if i < size n g then hist base n g m i else zero
def histLeft (base NL NR g m i : ℕ) : ℕ :=
  histogramPtr (leftBase base) NL g m (zeroBase base NL NR g m) i
def histRight (base NL NR g m i : ℕ) : ℕ :=
  histogramPtr (rightBase base NL g m) NR g m (zeroBase base NL NR g m) i
def count (NL NR g : ℕ) : ℕ := max (size NL g) (size NR g)
end ThreeSum.SourceBandPairSlices


