-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColorIndex
-- name    : Submission_ThreeSum_LightColorIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:37.445326+00:00
-- url     : https://prove2.me/theorems/9363a7d8-e23e-4289-97ad-9bd20c4cdb35
-- title:
--   Light Color Index
-- statement:
--   Definitions and structural lemmas for Light Color Index, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorIndex.lean

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_Coloring
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightColorIndex
open Light LightSubsetAddress
variable {lim : Limits} {P : Program}
def color {W : ℕ} (p : Coloring.Parameter W) (m : ℕ) : ℕ :=
  (p.2 (m.testBit p.1.1.val,m.testBit p.1.2.val)).val
def body (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 2,v 1,v 0,v 8] 9 ;;
  .call pErase [v 0,v 3,v 1,v 0,v 8] 10 ;;
  .ite (v 9 =' v 1)
    (.ite (v 10 =' v 1) (.set 0 (v 4)) (.set 0 (v 5)))
    (.ite (v 10 =' v 1) (.set 0 (v 6)) (.set 0 (v 7)))
def time (W : ℕ) : ℕ := 2*LightMaskErase.time W+150
def program : Program := [body 1,LightMaskErase.body 1]
end ThreeSum.LightColorIndex


