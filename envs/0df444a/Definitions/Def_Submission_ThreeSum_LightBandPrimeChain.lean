-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandPrimeChain
-- name    : Submission_ThreeSum_LightBandPrimeChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:33:32.620697+00:00
-- url     : https://prove2.me/theorems/5e182f62-5531-4c7f-a6d5-79eb0f30e330
-- title:
--   Light Band Prime Chain
-- statement:
--   Definitions and structural lemmas for Light Band Prime Chain, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeChain.lean

import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightBandPrimeChain
open Light BandCandidateRows BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
def body (pMinimum : ℕ) : Stmt :=
  .set 13 (k 1) ;;
  .set 16 (v 12 +' v 11 +' k 1) ;;
  .store (v 12) (v 13) ;;
  .for 14 (v 11) (
    .call pMinimum [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 13,v 9,v 10,v 16] 15 ;;
    .set 13 (v 13 *' v 15) ;;
    .store (v 12 +' v 14 +' k 1) (v 13)) ;;
  .set 0 (v 13)
def program : Program := LightBandPrimeMinimum.program ++ [body 17]
def time (maxMod g R s U levels : ℕ) : ℕ :=
  levels*(LightBandPrimeMinimum.time maxMod g R s U+140)+140
def space (free maxMod g U levels : ℕ) : ℕ :=
  LightWeightedScore.space (free+levels+1) maxMod g U
def Inv (μ : ℕ → ℤ) (qs : ℕ → ℕ)
    (a b c nA nB nC g recs R aux s levels free i : ℕ) (σ : State) : Prop :=
  ∃ (pval : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,aux,s,levels,free,
      qs i,i,pval,free+levels+1],ν⟩ ∧
    (∀ j ≤ i, ν (free+j)=(qs j : ℤ)) ∧ Kept μ ν free
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs aux s levels free maxMod U Y : ℕ}
end ThreeSum.LightBandPrimeChain


