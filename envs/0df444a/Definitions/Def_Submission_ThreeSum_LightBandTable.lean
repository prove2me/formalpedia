-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandTable
-- name    : Submission_ThreeSum_LightBandTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:30.539255+00:00
-- url     : https://prove2.me/theorems/4b9a8865-48ce-4d62-9763-aed149b0e2a5
-- title:
--   Light Band Table
-- statement:
--   Definitions and structural lemmas for Light Band Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandTable.lean

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightBandTable
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def rowValue (lo hi : ℕ → ℤ) (n : ℕ) (x s : ℤ) (f : ℕ → ℤ) (j : ℕ) : ℕ :=
  LightBandLookup.result lo hi n (s*x+f j)
def rowBody (pLookup : ℕ) : Stmt :=
  .for 10 (v 4) (
    .call pLookup [v 2,v 3,v 5,v 9 *' v 0 +' M (v 1 +' v 10),v 7,v 8] 11 ;;
    .store (v 6 +' v 10) (v 11))
def rowTime (n W : ℕ) : ℕ := n*(LightBandLookup.time W+60)+6
def body (pRow : ℕ) : Stmt :=
  .for 11 (v 4) (
    .call pRow [M (v 0 +' v 11),v 1,v 2,v 3,v 5,v 6,
      v 7 +' v 11 *' v 5,v 8,v 9,v 10] 12)
def time (nX nY W : ℕ) : ℕ := nX*(rowTime nY W+70)+6
def program : Program :=
  [body 1,rowBody 2,LightBandLookup.body 3,LightBandLookup.searchBody 3]
end ThreeSum.LightBandTable


