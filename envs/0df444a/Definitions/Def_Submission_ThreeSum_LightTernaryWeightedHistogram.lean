-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
-- name    : Submission_ThreeSum_LightTernaryWeightedHistogram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:39.706243+00:00
-- url     : https://prove2.me/theorems/f7d4be7f-0580-41f6-bdde-be3cecb913c2
-- title:
--   Light Ternary Weighted Histogram
-- statement:
--   Definitions and structural lemmas for Light Ternary Weighted Histogram, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
def total (key : ℕ → ℕ) (weight : ℕ → ℤ) (r n : ℕ) : ℤ :=
  ∑ i ∈ range n, if key i=r then weight i else 0
variable {lim : Limits} {P : Program} {d : ℕ}
def countBody : Stmt := .for 7 (v 3)
  (.store (v 4 +' M (v 0 +' v 7))
    (M (v 4 +' M (v 0 +' v 7)) +' M (v 2 +' M (v 1 +' k 2 *' v 7))))
def countTime (n : ℕ) : ℕ := 40*n+10
def body (pFill : ℕ) : Stmt := .call pFill [v 4,v 5,k 0] 8 ;; countBody
def time (n bank : ℕ) : ℕ := fillTime bank+countTime n+50
def program : Program := [body 1,fillBody]
end ThreeSum.LightTernaryWeightedHistogram


