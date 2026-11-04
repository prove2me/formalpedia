-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
-- name    : Submission_ThreeSum_LightSourceBucketOriginal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:34:42.159365+00:00
-- url     : https://prove2.me/theorems/8c28f722-1571-4fc3-a1d7-fb939cf0a886
-- title:
--   Light Source Bucket Original
-- statement:
--   Definitions and structural lemmas for Light Source Bucket Original, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketOriginal.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceBucketOriginal
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def body (pSource pBuckets : ℕ) : Stmt :=
  .call pSource [v 0,v 5,v 1,v 2,v 3,v 6,v 10,v 4] 11 ;;
  .call pBuckets [v 6,v 5,v 7,v 8,v 9,v 1,v 3] 11
def time (N p m U D : ℕ) : ℕ :=
  LightSourceHistogram.time N p m U D+LightSourceBucketFromHistogram.time N m+50
structure Procs (P : Program) (pMain : ℕ) where
  pSource : ℕ
  pBuckets : ℕ
  sourceProcs : LightSourceHistogram.Procs P pSource
  buckets : LightSourceBucketFromHistogram.Procs P pBuckets
  main : P[pMain]? = some (body pSource pBuckets)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 6,LightSourceHistogram.body 2 4,LightSourceResidues.body 3,emodBody,
    histogramBody 5,fillBody,LightSourceBucketFromHistogram.body 7 8,
    LightSourceBucketOffsets.body,LightSourceBucketScatter.body]
def programProcs : Procs program 0 :=
  ⟨1,6,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,⟨7,8,rfl,rfl,rfl⟩,rfl⟩
end ThreeSum.LightSourceBucketOriginal


