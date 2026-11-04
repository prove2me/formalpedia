-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
-- name    : Submission_ThreeSum_LightTernaryWeightedSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:25:29.340198+00:00
-- url     : https://prove2.me/theorems/1d24d1db-27be-41f7-96ea-58ebf50d8c71
-- title:
--   Light Ternary Weighted Sum
-- statement:
--   Definitions and structural lemmas for Light Ternary Weighted Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryWeightedSum
open Light Finset
def sum (weights keys : ℕ → ℕ) (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range n, (weights i : ℤ) * f (keys i)
def loopBody : Stmt :=
  .set 5 (v 5 +' M (v 0 +' v 6) *' M (v 2 +' M (v 1 +' v 6)))
def body : Stmt :=
  .set 5 (k 0) ;;
  .for 6 (v 3) loopBody ;;
  .set 0 (v 5)
def time (n : ℕ) : ℕ := 40*n+20
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightTernaryWeightedSum


