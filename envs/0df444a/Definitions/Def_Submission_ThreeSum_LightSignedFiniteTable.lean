-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
-- name    : Submission_ThreeSum_LightSignedFiniteTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:27.153318+00:00
-- url     : https://prove2.me/theorems/8d5a14da-818a-4d63-83b5-66dbb4383d85
-- title:
--   Light Signed Finite Table
-- statement:
--   Definitions and structural lemmas for Light Signed Finite Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedFiniteTable.lean

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSignedFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def literal (z : ℤ) : Expr := k z.toNat -' k (-z).toNat
def stores : ℕ → List ℤ → Stmt
  | _, [] => .skip
  | offset, x :: xs => .store (v 0 +' k offset) (literal x) ;; stores (offset+1) xs
def body (xs : List ℤ) : Stmt := stores 0 xs ;; .set 0 (k xs.length)
def program (xs : List ℤ) : Program := [body xs]
end ThreeSum.LightSignedFiniteTable


