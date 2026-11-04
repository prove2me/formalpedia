-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandPairData
-- name    : Submission_ThreeSum_SourceBandPairData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:56:30.860983+00:00
-- url     : https://prove2.me/theorems/ded7e6ec-e819-4cc0-bad1-459136c1af09
-- title:
--   Source Band Pair Data
-- statement:
--   Definitions and structural lemmas for Source Band Pair Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
namespace ThreeSum.SourceBandPairData
open Light BandPartition
def leftBase (base : ℕ) : ℕ := base+8
def rightBase (base NL g m : ℕ) : ℕ := SourceBandLayout.work (leftBase base) NL g m
def zeroBase (base NL NR g m : ℕ) : ℕ := SourceBandLayout.work (rightBase base NL g m) NR g m
def next (base NL NR g m : ℕ) : ℕ := zeroBase base NL NR g m+m+1
def header (base NL NR g m : ℕ) : List ℤ :=
  [leftBase base,size NL g,rightBase base NL g m,size NR g,
    zeroBase base NL NR g m,next base NL NR g m,NL,NR]
structure Data (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g p m : ℕ) (shift : ℤ) : Prop where
  left : ∀ i < size NL g, SourceBandData.At μ fL (leftBase base) NL g p m 0 i
  right : ∀ i < size NR g, SourceBandData.At μ fR (rightBase base NL g m) NR g p m shift i
  zero : ∀ r ≤ m, μ (zeroBase base NL NR g m+r)=0
structure Stored (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g p m : ℕ) (shift : ℤ)
    extends Data μ fL fR base NL NR g p m shift : Prop where
  heads : Seg μ base (header base NL NR g m)
end ThreeSum.SourceBandPairData


