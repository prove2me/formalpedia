-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryDivide
-- name    : Submission_ThreeSum_LightTernaryDivide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:39:29.792204+00:00
-- url     : https://prove2.me/theorems/91ef8aae-ba9b-428a-aaac-779b0f01500c
-- title:
--   Light Ternary Divide
-- statement:
--   Definitions and structural lemmas for Light Ternary Divide, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryDivide.lean

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Mathlib.Data.Int.Order.Lemmas
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def body (pDivide : ℕ) : Stmt :=
  .ite (v 0 <' k 0)
    (.call pDivide [k 0 -' v 0,v 1,v 2] 3 ;;
      .set 0 (k 0 -' v 3))
    (.call pDivide [v 0,v 1,v 2] 0)
def time (V : ℕ) : ℕ := LightOutputDecodeDivide.budget V + 50
def program : Program := [body 1,LightOutputDecodeDivide.body]
end ThreeSum.LightTernaryDivide


