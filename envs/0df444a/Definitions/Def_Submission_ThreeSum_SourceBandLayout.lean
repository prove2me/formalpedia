-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandLayout
-- name    : Submission_ThreeSum_SourceBandLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:34.5289+00:00
-- url     : https://prove2.me/theorems/620d46d5-233a-4853-98c5-dff9f1168f16
-- title:
--   Source Band Layout
-- statement:
--   Definitions and structural lemmas for Source Band Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandLayout.lean

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
set_option autoImplicit false
namespace ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
def cap (n g : ℕ) : ℕ := min n g
def len (n g i : ℕ) : ℕ := stop n g i-start g i
def stride (n g m : ℕ) : ℕ := 3*m+1+2*cap n g
def data (base n g : ℕ) : ℕ := base+6*size n g
def hist (base n g m i : ℕ) : ℕ := data base n g+i*stride n g m
def codes (base n g m i : ℕ) : ℕ := hist base n g m i+m
def offsets (base n g m i : ℕ) : ℕ := codes base n g m i+cap n g
def cursor (base n g m i : ℕ) : ℕ := offsets base n g m i+m+1
def flat (base n g m i : ℕ) : ℕ := cursor base n g m i+m
def work (base n g m : ℕ) : ℕ := hist base n g m (size n g)
def key (f : ℕ → ℤ) (g p m : ℕ) (shift : ℤ) (i j : ℕ) : ℕ :=
  LightSourceResidues.key p m shift (f (start g i+j))
end ThreeSum.SourceBandLayout


