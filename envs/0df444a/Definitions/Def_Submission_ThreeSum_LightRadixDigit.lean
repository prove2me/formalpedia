-- Prove2me | Definitions.Def_Submission_ThreeSum_LightRadixDigit
-- name    : Submission_ThreeSum_LightRadixDigit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:39:07.218725+00:00
-- url     : https://prove2.me/theorems/116cb9e3-4e7b-4556-8e3c-3674acdf79df
-- title:
--   Light Radix Digit
-- statement:
--   Definitions and structural lemmas for Light Radix Digit, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixDigit.lean

import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightRadixDigit
open Light
def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 0,v 1] 3 ;;
  .call pDivide [v 3,v 2] 4 ;;
  .set 0 (v 3 -' v 4 *' v 2)
def time (k : ℕ) : ℕ := 40*(k+1)+100
def word (k b p : ℕ) : ℕ := 4*(k+b+p+2)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightSmallDivide.body]
end ThreeSum.LightRadixDigit


