-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMinimum
-- name    : Submission_ThreeSum_LightMinimum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:14.590577+00:00
-- url     : https://prove2.me/theorems/45dd8e91-babb-4265-af30-91246d34338c
-- title:
--   Light Minimum
-- statement:
--   Definitions and structural lemmas for Light Minimum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_Balancing
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightMinimum
open Light
def least (f : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | n+1 => if f n < f (least f n) then n else least f n
def scanBody : Stmt :=
  .ite (M (v 0 +' v 3) <' M (v 0 +' v 2)) (.set 2 (v 3)) .skip
def body : Stmt :=
  .set 2 (k 0) ;;
  .for 3 (v 1) scanBody ;;
  .set 0 (v 2)
def time (n : ℕ) : ℕ := 32*n + 20
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightMinimum


