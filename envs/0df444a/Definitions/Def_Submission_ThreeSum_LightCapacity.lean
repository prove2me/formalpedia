-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCapacity
-- name    : Submission_ThreeSum_LightCapacity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:27:45.812267+00:00
-- url     : https://prove2.me/theorems/80afa6b1-4fb9-4896-b320-5f611745b417
-- title:
--   Light Capacity
-- statement:
--   Definitions and structural lemmas for Light Capacity, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCapacity.lean

import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightCapacity
open Light ThreeSum.KaratsubaInterface
variable {lim : Limits} {P : Program} {d : ℕ}
def body : Stmt :=
  .set 1 (k 0) ;;
  .set 2 (k 1) ;;
  .while (v 2 <' v 0) (
    .set 2 (v 2 +' v 2) ;;
    .set 1 (v 1 +' k 1)) ;;
  .set 0 (v 2)
def time (p : ℕ) : ℕ := 12 * Nat.clog 2 p + 10
def program : Program := [body]
end ThreeSum.LightCapacity


