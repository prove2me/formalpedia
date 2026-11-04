-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBucketOffsets
-- name    : Submission_ThreeSum_LightSourceBucketOffsets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:13.388509+00:00
-- url     : https://prove2.me/theorems/63c8ffe5-7279-42ea-bf00-cb3ee5449698
-- title:
--   Light Source Bucket Offsets
-- statement:
--   Definitions and structural lemmas for Light Source Bucket Offsets, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketOffsets.lean

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceBucketOffsets
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
def body : Stmt :=
  .set 6 (k 0) ;;
  .for 5 (v 3) (
    .store (v 1 +' v 5) (v 6) ;;
    .store (v 2 +' v 5) (v 6) ;;
    .set 6 (v 6 +' M (v 0 +' v 5))) ;;
  .store (v 1 +' v 3) (v 6)
def time (M : ℕ) : ℕ := 120*M+120
def Inv (μ : ℕ → ℤ) (key : ℕ → ℕ) (hist offsets cursor M N j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ, σ = ⟨frame [hist,offsets,cursor,M,N,j,offset key N j],ν⟩ ∧
    (∀ r < j, ν (offsets+r) = (offset key N r : ℤ) ∧
      ν (cursor+r) = (offset key N r : ℤ)) ∧
    SameOutside μ ν offsets (cursor+M-offsets)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightSourceBucketOffsets


