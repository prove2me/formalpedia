-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorSources
-- name    : Submission_ThreeSum_LightEncodedColorSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:00:37.924777+00:00
-- url     : https://prove2.me/theorems/523db6f7-b506-427e-8b9e-71db41ff4c27
-- title:
--   Light Encoded Color Sources
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Sources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorSources.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
import Definitions.Def_Submission_ThreeSum_EncodedColorCoverData
import Definitions.Def_Submission_ThreeSum_LightSourceFinitePrepared
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightEncodedColorSources
open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs
set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
def sourceBase (free p M h J : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  EncodedColorWantedData.nextFree (LightGuardedWanted.wantedFree free h J xs.length) M
    (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J) (3*xs.length)
    (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J : ℤ)
def body (pPower pSource : ℕ) : Stmt :=
  .set 11 (M (v 9 +' k 2)) ;;
  .set 12 (v 9 +' k 3) ;;
  .set 13 (M (v 10 +' k 6)) ;;
  .call pPower [v 13,v 1] 14 ;;
  .set 15 (M (v 10 +' k 8)) ;;
  .set 16 (M (v 10 +' k 7)) ;;
  .set 17 (M (v 10 +' k 10)) ;;
  .set 18 (M (v 10 +' k 12)) ;;
  .set 19 (M (v 10 +' k 13)) ;;
  .set 20 (M (v 10 +' k 14)) ;;
  .set 21 (M (v 10 +' k 15)) ;;
  .call pSource [v 1,v 15,v 0,v 13,v 16,v 2,v 14,v 18,v 19,v 20,v 21,
    v 3,v 4,v 5,v 6,v 7,v 8,v 12,v 11,v 17] 0
def program : Program := LightSourceControlsHostProgram.program ++ [body 74 79]
def time (NL NR g p h J cut U M : ℕ) : ℕ :=
  LightNatPower.time J+LightSourceControlsHost.time NL NR g p h J cut U M+1000
variable {lim : Limits} {d : ℕ}
end ThreeSum.LightEncodedColorSources


