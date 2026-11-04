-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
-- name    : Submission_ThreeSum_LightSourceOccurrenceArray
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:16:01.479627+00:00
-- url     : https://prove2.me/theorems/fe83a54c-f143-4281-a5c1-0e2bd292a2fc
-- title:
--   Light Source Occurrence Array
-- statement:
--   Definitions and structural lemmas for Light Source Occurrence Array, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceOccurrenceArray.lean

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourceOccurrenceArray
open Light OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def body (pDigits : ℕ) : Stmt :=
  .for 5 (v 0) (
    .call pDigits [v 5,v 1,v 2,v 3 +' v 5 *' v 1,v 4] 6)
def time (N J : ℕ) : ℕ := N*(LightOutputDecodeDigits.time J N+150)+10
def Inv (μ : ℕ → ℤ) (N J m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,J,m,dst,work,i,r],ν⟩ ∧
    (∀ j < i, ∀ s < J, ν (dst+j*J+s)=((indices m J j).getD s 0 : ℤ)) ∧
    Kept μ ν dst
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightOutputDecodeDigits.body 2,LightOutputDecodeDivide.body]
end ThreeSum.LightSourceOccurrenceArray


