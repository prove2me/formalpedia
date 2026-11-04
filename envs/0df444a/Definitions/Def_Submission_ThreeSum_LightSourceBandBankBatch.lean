-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandBankBatch
-- name    : Submission_ThreeSum_LightSourceBandBankBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:04:58.553416+00:00
-- url     : https://prove2.me/theorems/7d44e2f3-e4f8-4054-814d-054e07627ede
-- title:
--   Light Source Band Bank Batch
-- statement:
--   Definitions and structural lemmas for Light Source Band Bank Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBankBatch.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandBankStep
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceBandBankBatch
open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
def body (pStep : ℕ) : Stmt :=
  .for 18 (v 16) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
      v 13 +' v 18 *' v 17,v 14,v 15,v 18] 19)
def time (NL NR g h J cut : ℕ) : ℕ :=
  SourceBandPairSlices.count NL NR g*(LightSourceBandBankStep.time h J cut+200)+20
structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightSourceBandBankStep.Procs P pStep
  main : P[pMain]?=some (body pStep)
def Inv (μ : ℕ → ℤ) (fL fR : ℕ → ℤ)
    (pair NL NR g p h J cut occ maps candidates histL histR base : ℕ) (shift : ℤ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
      histL,histR,pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,
      SourceBandPairSlices.count NL NR g,span h J cut,i,r],ν⟩ ∧
    (∀ j < i, At ν fL fR base NL NR g h J cut (p : ℤ) shift j) ∧ Kept μ ν base
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceBandBankBatch


