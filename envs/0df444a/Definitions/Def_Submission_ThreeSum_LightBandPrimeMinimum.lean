-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
-- name    : Submission_ThreeSum_LightBandPrimeMinimum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:29:17.596465+00:00
-- url     : https://prove2.me/theorems/024ec1d0-45e3-4140-8159-27439d79d1cd
-- title:
--   Light Band Prime Minimum
-- statement:
--   Definitions and structural lemmas for Light Band Prime Minimum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeMinimum.lean

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightBandPrimeMinimum
open Light BandCandidateRows BandWeightedScore BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
def body (pScore : ℕ) : Stmt :=
  .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9 *' M (v 10),v 10,v 11,v 12] 13 ;;
  .set 14 (k 0) ;;
  .for 15 (v 11) (
    .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,
      v 9 *' M (v 10 +' v 15),v 10,v 11,v 12] 16 ;;
    .ite (v 16 <' v 13) (.set 13 (v 16) ;; .set 14 (v 15)) .skip) ;;
  .set 0 (M (v 10 +' v 14))
def program : Program := LightBandWeightedScore.program ++ [body 16]
def time (maxMod g R s U : ℕ) : ℕ :=
  LightBandWeightedScore.time maxMod g R s U+
    s*(LightBandWeightedScore.time maxMod g R s U+140)+140
def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (a b c nA nB nC g recs R q aux s free i : ℕ) (σ : State) : Prop :=
  ∃ (value : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,q,aux,s,free,
      f (LightMinimum.least f i),LightMinimum.least f i,i,value],ν⟩ ∧ Kept μ ν free
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}
end ThreeSum.LightBandPrimeMinimum


