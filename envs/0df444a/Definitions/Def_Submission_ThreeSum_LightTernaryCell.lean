-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryCell
-- name    : Submission_ThreeSum_LightTernaryCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:25.65474+00:00
-- url     : https://prove2.me/theorems/b35801b3-eed9-47a4-ba15-da8e2fe3ebca
-- title:
--   Light Ternary Cell
-- statement:
--   Definitions and structural lemmas for Light Ternary Cell, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCell.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryCell
open Light ThreeSum.TernaryQuery
variable {lim : Limits} {P : Program} {d : ℕ}
def zetaBody : Stmt :=
  .ite (v 0 =' k 0) (.set 0 (M (v 1)))
    (.ite (v 0 =' k 1) (.set 0 (M (v 1) +' M (v 2)))
      (.set 0 (M (v 1) +' k 2 *' M (v 2) +' M (v 3))))
def inverseBody : Stmt :=
  .ite (v 0 =' k 0) (.set 0 (M (v 1)))
    (.ite (v 0 =' k 1) (.set 0 (M (v 2) -' M (v 1)))
      (.set 0 (M (v 3) -' k 2 *' M (v 2) +' M (v 1))))
def time : ℕ := 80
def program : Program := [zetaBody, inverseBody]
end ThreeSum.LightTernaryCell


