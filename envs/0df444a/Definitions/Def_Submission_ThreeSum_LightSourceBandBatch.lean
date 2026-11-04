-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandBatch
-- name    : Submission_ThreeSum_LightSourceBandBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:59:11.163545+00:00
-- url     : https://prove2.me/theorems/c8687b61-9787-4576-958f-e4234fb602fa
-- title:
--   Light Source Band Batch
-- statement:
--   Definitions and structural lemmas for Light Source Band Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBatch.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandStep
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceBandBatch
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
def body (pStep : ℕ) : Stmt :=
  .for 12 (v 8) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12] 13)
def time (n g p m U D : ℕ) : ℕ :=
  size n g*(LightSourceBandStep.time n g p m U D+180)+20
structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightSourceBandStep.Procs P pStep
  main : P[pMain]? = some (body pStep)
def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ) (src n g p m base : ℕ) (shift : ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [src,n,g,p,m,shift,base,cap n g,size n g,data base n g,stride n g m,
      work base n g m,i,r],ν⟩ ∧
    (∀ j < i, SourceBandData.At ν f base n g p m shift j) ∧ Kept μ ν base
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceBandBatch


