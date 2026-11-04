-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
-- name    : Submission_ThreeSum_LightBandPrimeConstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:37:14.979559+00:00
-- url     : https://prove2.me/theorems/45769c0e-8d74-45ef-b006-ab45d79206f8
-- title:
--   Light Band Prime Construction
-- statement:
--   Definitions and structural lemmas for Light Band Prime Construction, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeConstruction.lean

import Definitions.Def_Submission_ThreeSum_LightBandPrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBandPrimeConstruction
open Light BandCandidateRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
def modulus (y nA nB nC g : ℕ) (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) : ℕ :=
  BandPrimeChoice.modulus (LightPrimePool.prime y) (LightPrimePool.size y)
    nA nB nC g A B C rs levels
def body (pPool pChain : ℕ) : Stmt :=
  .call pPool [v 9,v 11] 12 ;;
  .set 13 (v 11 +' k 3 *' v 9) ;;
  .call pChain [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 11,v 12,v 10,v 13] 0
def program : Program := ReportingHostRelocation.program
  LightPrimePool.program LightBandPrimeChain.program ++ [body 0 21]
def time (maxMod g R y U levels : ℕ) : ℕ :=
  LightPrimePool.time y+
    LightBandPrimeChain.time maxMod g R (LightPrimePool.size y) U levels+140
def space (free maxMod g y U levels : ℕ) : ℕ :=
  max (LightPrimePool.space free y)
    (LightBandPrimeChain.space (free+3*y) maxMod g U levels)
def word (maxMod nA nB nC g R y U : ℕ) : ℕ :=
  max (LightPrimePool.word y)
    (LightBandWeightedScore.word maxMod nA nB nC g R (LightPrimePool.size y) U)
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}
end ThreeSum.LightBandPrimeConstruction


