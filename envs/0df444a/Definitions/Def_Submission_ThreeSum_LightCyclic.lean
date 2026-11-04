-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCyclic
-- name    : Submission_ThreeSum_LightCyclic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:27:50.257383+00:00
-- url     : https://prove2.me/theorems/b597117f-f069-40a8-9900-9b0f0211be87
-- title:
--   Light Cyclic
-- statement:
--   Definitions and structural lemmas for Light Cyclic, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}
def body (pMultiply pLinear : ℕ) : Stmt :=
  .call pMultiply [v 0, v 1, v 2, v 3, v 5] 7 ;;
  .call pLinear [v 3, v 3 +' v 6, v 4, v 6, k 1] 7
def combinedTime (k p : ℕ) : ℕ := LightKaratsuba.time k + LightArray.linearTime p + 100
def program : Program :=
  [body 1 3, LightKaratsuba.body 1 2 3 4, halfBody, LightArray.linearBody, fillBody]
end ThreeSum.LightCyclic


