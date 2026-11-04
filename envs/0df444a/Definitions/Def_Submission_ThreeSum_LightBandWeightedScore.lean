-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
-- name    : Submission_ThreeSum_LightBandWeightedScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:26:13.107076+00:00
-- url     : https://prove2.me/theorems/1bc9486e-7c7c-4228-b87b-969792fb4ffd
-- title:
--   Light Band Weighted Score
-- statement:
--   Definitions and structural lemmas for Light Band Weighted Score, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScore.lean

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreCell
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBandWeightedScore
open Light BandCandidateRows BandWeightedScore
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
def body (pCell : ℕ) : Stmt :=
  .set 13 (k 0) ;;
  .for 14 (v 8) (
    .call pCell [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7 +' k 4 *' v 14,v 9,v 10,v 11,v 12] 15 ;;
    .set 13 (v 13 +' v 15)) ;;
  .set 0 (v 13)
def program : Program := LightBandWeightedScoreCell.program ++ [body 15]
def time (maxMod g R s U : ℕ) : ℕ := R*(LightBandWeightedScoreCell.time maxMod g s U+100)+50
def word (maxMod nA nB nC g R s U : ℕ) : ℕ :=
  LightBandWeightedScoreCell.word maxMod nA nB nC g s U+R*(s*g^3)+R+8
def Inv (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (a b c nA nB nC g recs R q aux s free i : ℕ) (σ : State) : Prop :=
  ∃ (value : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,q,aux,s,free,f i,i,value],ν⟩ ∧ Kept μ ν free
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}
end ThreeSum.LightBandWeightedScore


