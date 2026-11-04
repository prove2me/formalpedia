-- Prove2me | Definitions.Def_Submission_ThreeSum_LightWantedRow
-- name    : Submission_ThreeSum_LightWantedRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:49.946342+00:00
-- url     : https://prove2.me/theorems/663b2592-b08a-4bcc-859e-2649d3f2133d
-- title:
--   Light Wanted Row
-- statement:
--   Definitions and structural lemmas for Light Wanted Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedRow.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightWantedRow
open Light
set_option maxHeartbeats 900000
def body : Stmt :=
  .for 6 (v 3) (
    .store (v 4 +' k 2 *' (v 5 +' v 6)) (v 0) ;;
    .store (v 4 +' k 2 *' (v 5 +' v 6) +' k 1) (M (v 1 +' v 2 +' v 6)))
def time (n : ℕ) : ℕ := 120*n+20
def Inv (μ : ℕ → ℤ) (left src start n dst previous j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ, σ=⟨frame [left,src,start,n,dst,previous,j],ν⟩ ∧
    (∀ t < j, ν (dst+2*(previous+t))=(left : ℤ) ∧
      ν (dst+2*(previous+t)+1)=μ (src+start+t)) ∧
    SameOutside μ ν (dst+2*previous) (2*n)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightWantedRow


