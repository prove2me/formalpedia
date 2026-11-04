-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColorArray
-- name    : Submission_ThreeSum_LightColorArray
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:34:05.127115+00:00
-- url     : https://prove2.me/theorems/c377783f-62fd-4eb4-97aa-b52e94ed7c6f
-- title:
--   Light Color Array
-- statement:
--   Definitions and structural lemmas for Light Color Array, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorArray.lean

import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightColorArray
open Light LightSubsetAddress
set_option maxHeartbeats 1200000
def body (pPowers pColor : ℕ) : Stmt :=
  .call pPowers [v 9,v 0 +' k 1,k 2] 10 ;;
  .for 11 (v 1) (
    .call pColor [v 0,v 11,v 2,v 3,v 4,v 5,v 6,v 7,v 9] 12 ;;
    .store (v 8 +' v 11) (v 12))
def time (W n : ℕ) : ℕ := powTableTime (W+1)+n*(LightColorIndex.time W+100)+100
def Inv {W : ℕ} (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (n dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      dst,work,powRet,j,r],ν⟩ ∧
    (∀ i < j, ν (dst+i) = (LightColorIndex.color p i : ℤ)) ∧
    Powers ν work W ∧ KeptBut μ ν work dst n
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 2,powTableBody,LightColorIndex.body 3,LightMaskErase.body 3]
end ThreeSum.LightColorArray


