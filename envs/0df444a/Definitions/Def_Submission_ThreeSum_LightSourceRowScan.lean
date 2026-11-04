-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceRowScan
-- name    : Submission_ThreeSum_LightSourceRowScan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:48.733959+00:00
-- url     : https://prove2.me/theorems/12f598d4-155c-438f-ad69-40ca53b0d611
-- title:
--   Light Source Row Scan
-- statement:
--   Definitions and structural lemmas for Light Source Row Scan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRowScan.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceRowScan
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def count (bits : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, bits i
def hash (bits w0 w1 : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, if bits i=1 then w1 i else w0 i
def roundBody : Stmt :=
  .set 9 (M (v 0 +' v 8)) ;;
  .set 5 (v 5 +' v 9) ;;
  .ite (v 9 =' k 1)
    (.set 6 (v 6 +' M (v 2 +' v 8)) ;;
      .set 7 (v 7 +' M (v 1 +' v 8)))
    (.set 6 (v 6 +' M (v 1 +' v 8)) ;;
      .set 7 (v 7 +' M (v 2 +' v 8)))
def body : Stmt :=
  .set 5 (k 0) ;;
  .set 6 (k 0) ;;
  .set 7 (k 0) ;;
  .for 8 (v 3) roundBody ;;
  .store (v 4) (v 5) ;;
  .store (v 4 +' k 1) (v 6) ;;
  .store (v 4 +' k 2) (v 7)
def time (L : ℕ) : ℕ := 150*L+100
def word (L U : ℕ) : ℕ := (L+1)*(U+1)+1
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightSourceRowScan


