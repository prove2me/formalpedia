-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryCodes
-- name    : Submission_ThreeSum_LightTernaryCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:41.050935+00:00
-- url     : https://prove2.me/theorems/6e644fb6-e678-41fd-97a5-e9fb880e5169
-- title:
--   Light Ternary Codes
-- statement:
--   Definitions and structural lemmas for Light Ternary Codes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCodes.lean

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
namespace ThreeSum.LightTernaryCodes
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
variable {lim : Limits} {P : Program}
def zeroCode (W low high m : ℕ) : ℕ := eraseMask W low (eraseMask W high m)
def oneCode (W high m : ℕ) : ℕ := eraseMask W high m
def digit (W low high m : ℕ) : ℕ :=
  LightMaskBits.bit W m low + LightMaskBits.bit W m high
def zeroBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 2,v 3,v 0,v 4] 5 ;;
  .call pErase [v 0,v 1,v 5,v 0,v 4] 0
def zeroTime (W : ℕ) : ℕ := 2*LightMaskErase.time W + 80
def digitBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 1,v 3,v 0,v 4] 5 ;;
  .call pErase [v 0,v 2,v 3,v 0,v 4] 6 ;;
  .set 7 (k 0) ;;
  .ite (v 5 =' v 3) .skip (.set 7 (k 1)) ;;
  .ite (v 6 =' v 3) .skip (.set 7 (v 7 +' k 1)) ;;
  .set 0 (v 7)
def digitTime (W : ℕ) : ℕ := 2*LightMaskErase.time W + 130
def program : Program := [zeroBody 2,digitBody 2,LightMaskErase.body 2]
end ThreeSum.LightTernaryCodes


