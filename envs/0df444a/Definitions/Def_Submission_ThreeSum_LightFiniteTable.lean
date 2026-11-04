-- Prove2me | Definitions.Def_Submission_ThreeSum_LightFiniteTable
-- name    : Submission_ThreeSum_LightFiniteTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:26:46.721818+00:00
-- url     : https://prove2.me/theorems/e653dbe4-2900-447c-a7e9-4b0756db546c
-- title:
--   Light Finite Table
-- statement:
--   Definitions and structural lemmas for Light Finite Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFiniteTable.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def stores : ℕ → List ℕ → Stmt
  | _, [] => .skip
  | offset, x :: xs => .store (v 0 +' k offset) (k x) ;; stores (offset+1) xs
def body (xs : List ℕ) : Stmt := stores 0 xs ;; .set 0 (k xs.length)
def program (xs : List ℕ) : Program := [body xs]
end ThreeSum.LightFiniteTable


