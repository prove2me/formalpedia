-- Prove2me | Definitions.Def_Submission_ThreeSum_LightArgumentTable
-- name    : Submission_ThreeSum_LightArgumentTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:39.591063+00:00
-- url     : https://prove2.me/theorems/c60309eb-45ff-40a0-bdea-91477fb69ba3
-- title:
--   Light Argument Table
-- statement:
--   Definitions and structural lemmas for Light Argument Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArgumentTable.lean

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightArgumentTable
open Light
def stores (offset : ℕ) : ℕ → Stmt
  | 0 => .skip
  | n+1 => .store (v 0 +' k offset) (v (offset+1)) ;; stores (offset+1) n
variable {lim : Limits} {P : Program} {depth : ℕ}
end ThreeSum.LightArgumentTable


