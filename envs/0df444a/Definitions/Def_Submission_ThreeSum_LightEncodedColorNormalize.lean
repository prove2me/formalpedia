-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorNormalize
-- name    : Submission_ThreeSum_LightEncodedColorNormalize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:37:48.26825+00:00
-- url     : https://prove2.me/theorems/20f3fa71-cad3-45ce-8d83-a896741534b4
-- title:
--   Light Encoded Color Normalize
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Normalize, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorNormalize.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightEncodedColorNormalize
open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData
set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
def body (pLayout pColor : ℕ) : Stmt :=
  .set 5 (M (v 2) +' k 1) ;;
  .set 6 (M (v 2 +' k 17)) ;;
  .call pLayout [v 1,v 6,v 4] 7 ;;
  .set 8 (v 4 +' k 8) ;;
  .set 9 (v 8 +' v 1) ;;
  .set 10 (v 9 +' v 1 +' k 1) ;;
  .set 11 (v 10 +' v 1 +' k 1) ;;
  .set 12 (M (v 4)) ;;
  .set 13 (M (v 4 +' k 1)) ;;
  .set 14 (M (v 4 +' k 2)) ;;
  .set 15 (M (v 4 +' k 3)) ;;
  .set 16 (M (v 4 +' k 4)) ;;
  .set 17 (M (v 4 +' k 5)) ;;
  .set 18 (M (v 4 +' k 6)) ;;
  .set 19 (M (v 4 +' k 7)) ;;
  .set 20 (v 17 +' k 2 +' k 2 *' v 1) ;;
  .set 21 (M (v 3)) ;;
  .set 22 (M (v 3 +' k 1)) ;;
  .set 23 (M (v 3 +' k 2)) ;;
  .set 24 (M (v 3 +' k 3)) ;;
  .set 25 (M (v 3 +' k 4)) ;;
  .set 26 (M (v 3 +' k 5)) ;;
  .call pColor [v 0,v 1,v 5,v 21,v 22,v 23,v 24,v 25,v 26,v 8,v 9,v 10,v 11,v 6,
    v 12,v 13,v 14,v 15,v 16,v 17,v 20,v 18,v 19] 27 ;;
  .store (v 7) (v 27) ;;
  .set 0 (v 7)
def program : Program := LightBandRawAColor.program ++ [LightEncodedColorLayout.body 9,body 44 43]
def time (n : ℕ) : ℕ := LightEncodedColorLayout.time n (bandSize n)+
  LightBandRawAColor.time (inputBits n+1) n (bandSize n)+1200
def space (free n : ℕ) : ℕ :=
  LightBandRawAColor.space (tables free n) (vals free n (bandSize n)) (inputBits n+1) n (bandSize n)+1
def word (n U : ℕ) : ℕ :=
  LightBandRawAColor.word (inputBits n+1) n (bandSize n) U+
    LightEncodedColorLayout.word n (bandSize n)+(inputBits n+1)+100
variable {lim : Limits} {d : ℕ}
end ThreeSum.LightEncodedColorNormalize


