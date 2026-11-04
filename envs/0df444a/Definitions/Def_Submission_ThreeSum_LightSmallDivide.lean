-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSmallDivide
-- name    : Submission_ThreeSum_LightSmallDivide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:38:27.523889+00:00
-- url     : https://prove2.me/theorems/f56de4b0-b2fc-4047-9e12-e19c0dbfddfe
-- title:
--   Light Small Divide
-- statement:
--   Definitions and structural lemmas for Light Small Divide, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSmallDivide.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSmallDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def body : Stmt :=
  .ite (k 0 <' v 1)
    (.set 2 (k 0) ;;
      .while ((v 2 +' k 1) *' v 1 ≤' v 0) (.set 2 (v 2 +' k 1)) ;;
      .set 0 (v 2))
    (.set 0 (k 0))
def time (a b : ℕ) : ℕ := 20*(a/b+1)+20
def program : Program := [body]
end ThreeSum.LightSmallDivide


