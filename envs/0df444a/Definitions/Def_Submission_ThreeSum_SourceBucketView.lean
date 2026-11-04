-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBucketView
-- name    : Submission_ThreeSum_SourceBucketView
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:27:19.852026+00:00
-- url     : https://prove2.me/theorems/e2d93fde-55e6-462d-892d-d0c8f1989fc1
-- title:
--   Source Bucket View
-- statement:
--   Definitions and structural lemmas for Source Bucket View, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBucketView.lean

import Definitions.Def_Submission_ThreeSum_SourceBuckets
set_option autoImplicit false
namespace ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
def start (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := (μ (offsets+r)).toNat
def stop (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := (μ (offsets+r+1)).toNat
def length (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := stop μ offsets r-start μ offsets r
def indices (μ : ℕ → ℤ) (offsets flat r : ℕ) : List ℕ :=
  bucketList μ flat (start μ offsets r) (length μ offsets r)
end ThreeSum.SourceBucketView


