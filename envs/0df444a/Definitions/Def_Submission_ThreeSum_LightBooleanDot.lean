-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBooleanDot
-- name    : Submission_ThreeSum_LightBooleanDot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:19:59.307665+00:00
-- url     : https://prove2.me/theorems/0d71bee6-33d7-438e-aa54-5cddc735fb67
-- title:
--   Light Boolean Dot
-- statement:
--   Definitions and structural lemmas for Light Boolean Dot, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators
def dot (f g : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, f i * g i
def loopBody : Stmt :=
  .set 3 (v 3 +' M (v 0 +' v 4) *' M (v 1 +' v 4))
def body : Stmt :=
  .set 3 (k 0) ;;
  .for 4 (v 2) loopBody ;;
  .set 0 (v 3)
def time (n : ℕ) : ℕ := 32*n+20
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightBooleanDot


