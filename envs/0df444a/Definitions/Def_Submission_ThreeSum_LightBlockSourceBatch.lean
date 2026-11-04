-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
-- name    : Submission_ThreeSum_LightBlockSourceBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:38:48.947195+00:00
-- url     : https://prove2.me/theorems/730b1958-f9e8-49b6-8119-e0de3b4e685b
-- title:
--   Light Block Source Batch
-- statement:
--   Definitions and structural lemmas for Light Block Source Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBatch.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchStep
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightBlockSourceBatch
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
structure BankAt {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J : ℕ} (μ : ℕ → ℤ) (base count cut i : ℕ) (P shift : ℤ)
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) (q : GlobalOutput h J) : Prop where
  left : LightZetaStages.StoredThrough μ (leftBase base count (J*(512*h)) cut i) cut
    (BlockIndexedQuery.leftSource P B b q) (J*(512*h))
  right : LightZetaStages.StoredThrough μ (rightBase base count (J*(512*h)) cut i) cut
    (BlockIndexedQuery.rightSource P shift A a q) (J*(512*h))
  headerLeft : μ (base+2*i) = (leftBase base count (J*(512*h)) cut i : ℤ)
  headerRight : μ (base+2*i+1) = (rightBase base count (J*(512*h)) cut i : ℤ)
def body (pStep : ℕ) : Stmt :=
  .for 23 (v 16) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7 +' v 23 *' v 0,
      v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23] 24)
def time (count h J cut : ℕ) : ℕ := count*(LightBlockSourceBatchStep.time h J cut+200)+20
structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightBlockSourceBatchStep.Procs P pStep
  main : P[pMain]? = some (body pStep)
def Inv {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (μ : ℕ → ℤ) (h J cut occ maps candidates histL histR sourceHistL sourceHistR base count : ℕ)
    (p shift : ℤ) (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : ℕ → GlobalOutput h J) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
      histL,histR,sourceHistL,sourceHistR,base,downsetCap (J*(512*h)) cut,count,
      banks base count,stride (J*(512*h)) cut,maskBase base count (J*(512*h)) cut,
      bitBase base count (J*(512*h)) cut,rowOut base count (J*(512*h)) cut,
      work base count (J*(512*h)) cut,i,r],ν⟩ ∧
    (∀ j < i, BankAt ν base count cut j p shift B b A a (q j)) ∧ Kept μ ν base
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightBlockSourceBatch


