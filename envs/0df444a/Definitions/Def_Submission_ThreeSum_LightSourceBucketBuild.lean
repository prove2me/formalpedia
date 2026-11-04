-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
-- name    : Submission_ThreeSum_LightSourceBucketBuild
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:34:58.224871+00:00
-- url     : https://prove2.me/theorems/4dafb1a1-3507-4e7d-96be-e6d3d971edcb
-- title:
--   Light Source Bucket Build
-- statement:
--   Definitions and structural lemmas for Light Source Bucket Build, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketBuild.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceBucketBuild
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
def body (pHistogram pBuckets : ℕ) : Stmt :=
  .call pHistogram [v 0,v 1,v 5,v 6] 7 ;;
  .call pBuckets [v 0,v 1,v 2,v 3,v 4,v 5,v 6] 7
def time (N M : ℕ) : ℕ := histogramTime N M+LightSourceBucketFromHistogram.time N M+50
structure Procs (P : Program) (pMain : ℕ) where
  pHistogram : ℕ
  pFill : ℕ
  pBuckets : ℕ
  histogram : P[pHistogram]? = some (histogramBody pFill)
  fill : P[pFill]? = some fillBody
  buckets : LightSourceBucketFromHistogram.Procs P pBuckets
  main : P[pMain]? = some (body pHistogram pBuckets)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 3,histogramBody 2,fillBody,LightSourceBucketFromHistogram.body 4 5,
    LightSourceBucketOffsets.body,LightSourceBucketScatter.body]
def programProcs : Procs program 0 := ⟨1,2,3,rfl,rfl,⟨4,5,rfl,rfl,rfl⟩,rfl⟩
end ThreeSum.LightSourceBucketBuild


