-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBalancedOffset
-- name    : Submission_ThreeSum_LightBalancedOffset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:37.363281+00:00
-- url     : https://prove2.me/theorems/a67bd8e9-2cfe-4a7c-ae44-1c269d121264
-- title:
--   Light Balanced Offset
-- statement:
--   Definitions and structural lemmas for Light Balanced Offset, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators
def offset {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) : ℕ :=
  LightMinimum.least (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) p
def body (pCyclic pMinimum : ℕ) : Stmt :=
  .call pCyclic [v 0, v 1, v 2, v 3, v 4, v 5, v 6] 7 ;;
  .call pMinimum [v 4, v 6] 0
def time (k p : ℕ) : ℕ :=
  LightCyclic.combinedTime k p + LightMinimum.time p + 100
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 6, LightCyclic.body 2 4, LightKaratsuba.body 2 3 4 5,
    halfBody, LightArray.linearBody, fillBody, LightMinimum.body]
end ThreeSum.LightBalancedOffset


