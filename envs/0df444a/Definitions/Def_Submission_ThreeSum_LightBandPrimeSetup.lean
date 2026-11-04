-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
-- name    : Submission_ThreeSum_LightBandPrimeSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:41:25.853204+00:00
-- url     : https://prove2.me/theorems/327e10b1-a796-4fd6-ba59-80cec52b77d5
-- title:
--   Light Band Prime Setup
-- statement:
--   Definitions and structural lemmas for Light Band Prime Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeSetup.lean

import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightBandPrimeSetup
open Light BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
def body (pDepth pConstruct : ℕ) : Stmt :=
  .call pDepth [v 9,v 10] 12 ;;
  .call pConstruct [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 10,v 12,v 11] 0
def program : Program := ReportingHostRelocation.program
  LightBandPrimeDepth.program LightBandPrimeConstruction.program ++ [body 0 23]
def time (maxMod g count M y U : ℕ) : ℕ := LightBandPrimeDepth.time M y+
  LightBandPrimeConstruction.time maxMod g count y U (LightBandPrimeDepth.depth M y)+100
def space (free maxMod g M y U : ℕ) : ℕ :=
  LightBandPrimeConstruction.space free maxMod g y U (LightBandPrimeDepth.depth M y)
def word (maxMod nA nB nC g count M y U : ℕ) : ℕ :=
  max (LightBandPrimeDepth.word M y)
    (LightBandPrimeConstruction.word maxMod nA nB nC g count y U)
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}
end ThreeSum.LightBandPrimeSetup


