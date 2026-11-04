-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBucketScatter
-- name    : Submission_ThreeSum_LightSourceBucketScatter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:17.490141+00:00
-- url     : https://prove2.me/theorems/a0989e6d-02cf-4c01-8722-ffb9b1310a9f
-- title:
--   Light Source Bucket Scatter
-- statement:
--   Definitions and structural lemmas for Light Source Bucket Scatter, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketScatter.lean

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceBucketScatter
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def body : Stmt :=
  .for 5 (v 3) (
    .set 6 (M (v 0 +' v 5)) ;;
    .set 7 (M (v 1 +' v 6)) ;;
    .store (v 2 +' v 7) (v 5) ;;
    .store (v 1 +' v 6) (v 7 +' k 1))
def time (N : ℕ) : ℕ := 120*N+20
def Inv (μ : ℕ → ℤ) (key : ℕ → ℕ) (keys cursor flat N M i : ℕ) (σ : State) : Prop :=
  ∃ (k q : ℤ) (ν : ℕ → ℤ), σ = ⟨frame [keys,cursor,flat,N,M,i,k,q],ν⟩ ∧
    (∀ r < M, ν (cursor+r) = ((offset key N r+count key r i : ℕ) : ℤ)) ∧
    (∀ j < i, ν (flat+position key N j) = (j : ℤ)) ∧
    SameOutside μ ν cursor (flat+N-cursor)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightSourceBucketScatter


