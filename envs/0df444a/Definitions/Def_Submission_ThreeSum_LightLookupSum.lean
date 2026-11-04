-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLookupSum
-- name    : Submission_ThreeSum_LightLookupSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:24.963547+00:00
-- url     : https://prove2.me/theorems/f2699222-d8bc-456f-bdcb-e4b1af841909
-- title:
--   Light Lookup Sum
-- statement:
--   Definitions and structural lemmas for Light Lookup Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators
def prefixSum (f : ℕ → ℕ) (key : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, f (key i)
def loopBody : Stmt :=
  .set 4 (v 4 +' M (v 1 +' M (v 0 +' v 5)))
def body : Stmt :=
  .set 4 (k 0) ;;
  .for 5 (v 2) loopBody ;;
  .set 0 (v 4)
def time (n : ℕ) : ℕ := 24*n+20
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightLookupSum


