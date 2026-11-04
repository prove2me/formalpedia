-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
-- name    : Submission_ThreeSum_LightTernaryEulerRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:38.630798+00:00
-- url     : https://prove2.me/theorems/4a2f2e23-39a8-423b-8241-408892647fd2
-- title:
--   Light Ternary Euler Row
-- statement:
--   Definitions and structural lemmas for Light Ternary Euler Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerRow.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryEulerRow
open Light
def body (pSum pDivide : ℕ) : Stmt :=
  .call pSum [v 0,v 1,v 2,v 3,v 4] 7 ;;
  .call pDivide [v 7,v 5,v 6] 0
def time (N V : ℕ) : ℕ :=
  LightTernaryWeightedSum.time N + LightTernaryDivide.time V + 100
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 2,LightTernaryWeightedSum.body,
  LightTernaryDivide.body 3,LightOutputDecodeDivide.body]
def fillBody (pRow : ℕ) : Stmt :=
  .call pRow [v 0,v 1,v 2,v 3,v 4,v 5,v 6] 8 ;;
  .store (v 7) (v 8) ;;
  .set 0 (v 8)
def fillTime (N V : ℕ) : ℕ := time N V+100
end ThreeSum.LightTernaryEulerRow


