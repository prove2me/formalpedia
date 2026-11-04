-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
-- name    : Submission_ThreeSum_LightSourceBucketFromHistogram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:31:55.468943+00:00
-- url     : https://prove2.me/theorems/8955a2c8-9198-4192-b76e-c546ba77c1e4
-- title:
--   Light Source Bucket From Histogram
-- statement:
--   Definitions and structural lemmas for Light Source Bucket From Histogram, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketFromHistogram.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBucketOffsets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketScatter
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceBucketFromHistogram
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def body (pOffsets pScatter : ℕ) : Stmt :=
  .call pOffsets [v 1,v 2,v 3,v 6,v 5] 7 ;;
  .call pScatter [v 0,v 3,v 4,v 5,v 6] 7
def time (N M : ℕ) : ℕ :=
  LightSourceBucketOffsets.time M+LightSourceBucketScatter.time N+80
structure Procs (P : Program) (pMain : ℕ) where
  pOffsets : ℕ
  pScatter : ℕ
  offsets : P[pOffsets]? = some LightSourceBucketOffsets.body
  scatter : P[pScatter]? = some LightSourceBucketScatter.body
  main : P[pMain]? = some (body pOffsets pScatter)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 2,LightSourceBucketOffsets.body,LightSourceBucketScatter.body]
def programProcs : Procs program 0 := ⟨1,2,rfl,rfl,rfl⟩
end ThreeSum.LightSourceBucketFromHistogram


