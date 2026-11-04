-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeCore
-- name    : Submission_ThreeSum_LightEncodedColorPrimeCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:45:51.31456+00:00
-- url     : https://prove2.me/theorems/0c95ccad-364d-40f1-a024-a90b5ca87e0c
-- title:
--   Light Encoded Color Prime Core
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Prime Core, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrimeCore.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightEncodedColorPrimeCore
open Light BandCandidateRows EncodedColorPrimeData
set_option maxHeartbeats 2600000
set_option maxRecDepth 13000
def body (pDepth pPool pChain : ℕ) : Stmt :=
  .call pDepth [v 9,v 10] 12 ;;
  .set 13 (v 11 +' k 6) ;;
  .call pPool [v 10,v 13] 14 ;;
  .set 15 (v 13 +' k 3 *' v 10) ;;
  .call pChain [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 13,v 14,v 12,v 15] 16 ;;
  .set 17 (v 15 +' v 12 +' k 1) ;;
  .store (v 11) (v 16) ;;
  .store (v 11 +' k 1) (v 12) ;;
  .store (v 11 +' k 2) (v 17) ;;
  .store (v 11 +' k 3) (v 13) ;;
  .store (v 11 +' k 4) (v 14) ;;
  .store (v 11 +' k 5) (v 15) ;;
  .set 0 (v 16)
def poolProgram : Program := ReportingHostRelocation.program LightBandPrimeDepth.program LightPrimePool.program
def joinedProgram : Program := ReportingHostRelocation.program poolProgram LightBandPrimeChain.program
def program : Program := joinedProgram ++ [body 0 1 22]
def time (maxMod g count M y U : ℕ) : ℕ :=
  LightBandPrimeDepth.time M y+LightPrimePool.time y+
    LightBandPrimeChain.time maxMod g count (LightPrimePool.size y) U (LightBandPrimeDepth.depth M y)+1000
def space (free maxMod g M y U : ℕ) : ℕ :=
  max (LightPrimePool.space (poolBase free) y)
    (LightBandPrimeChain.space (prefixBase free y) maxMod g U (LightBandPrimeDepth.depth M y))
def word (maxMod nA nB nC g count M y U : ℕ) : ℕ :=
  max (LightBandPrimeDepth.word M y)
    (max (LightPrimePool.word y)
      (LightBandWeightedScore.word maxMod nA nB nC g count (LightPrimePool.size y) U))
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}
end ThreeSum.LightEncodedColorPrimeCore


