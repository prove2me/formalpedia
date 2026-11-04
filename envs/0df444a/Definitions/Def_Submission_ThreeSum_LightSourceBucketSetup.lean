-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
-- name    : Submission_ThreeSum_LightSourceBucketSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:48.489522+00:00
-- url     : https://prove2.me/theorems/088dfba9-6e59-42bc-8467-b937765ff8aa
-- title:
--   Light Source Bucket Setup
-- statement:
--   Definitions and structural lemmas for Light Source Bucket Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketSetup.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSourceBucketSetup
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def hist (base : ℕ) : ℕ := base
def offsets (base M : ℕ) : ℕ := base+M
def cursor (base M : ℕ) : ℕ := base+2*M+1
def flat (base M : ℕ) : ℕ := base+3*M+1
def next (base N M : ℕ) : ℕ := base+3*M+1+N
def body (pBuild : ℕ) : Stmt :=
  .set 4 (v 3 +' v 2) ;;
  .set 5 (v 3 +' k 2 *' v 2 +' k 1) ;;
  .set 6 (v 3 +' k 3 *' v 2 +' k 1) ;;
  .set 7 (v 6 +' v 1) ;;
  .call pBuild [v 0,v 3,v 4,v 5,v 6,v 1,v 2] 8 ;;
  .set 0 (v 7)
def time (N M : ℕ) : ℕ := LightSourceBucketBuild.time N M+200
structure Procs (P : Program) (pMain : ℕ) where
  pBuild : ℕ
  build : LightSourceBucketBuild.Procs P pBuild
  main : P[pMain]? = some (body pBuild)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1,LightSourceBucketBuild.body 2 4,histogramBody 3,fillBody,
    LightSourceBucketFromHistogram.body 5 6,LightSourceBucketOffsets.body,LightSourceBucketScatter.body]
def programProcs : Procs program 0 :=
  ⟨1,⟨2,3,4,rfl,rfl,⟨5,6,rfl,rfl,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightSourceBucketSetup


