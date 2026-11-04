-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
-- name    : Submission_ThreeSum_LightOutputDecodeDigits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:12:04.985375+00:00
-- url     : https://prove2.me/theorems/dbb27b4f-ddfe-454e-a067-57d197248bcc
-- title:
--   Light Output Decode Digits
-- statement:
--   Definitions and structural lemmas for Light Output Decode Digits, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDigits.lean

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightOutputDecodeDigits
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
def body (pDivide : ℕ) : Stmt :=
  .set 5 (v 0) ;;
  .for 6 (v 1) (
    .call pDivide [v 5,v 2,v 4] 7 ;;
    .set 8 (v 5 -' v 7 *' v 2) ;;
    .store (v 3 +' v 1 -' k 1 -' v 6) (v 8) ;;
    .set 5 (v 7)) ;;
  .set 0 (v 5)
def time (J V : ℕ) : ℕ := J*(LightOutputDecodeDivide.budget V+100)+30
def word (V m J : ℕ) : ℕ := 4*V+4*m+4*J+32
def space (work V : ℕ) : ℕ := work+(Nat.log 2 (V+1)+2)
def Inv (μ : ℕ → ℤ) (k J m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (q r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [k,J,m,dst,work,(k/m^i : ℕ),i,q,r],ν⟩ ∧
    (∀ j < i, ν (dst+J-1-j)=(((k/m^j)%m : ℕ) : ℤ)) ∧
    Kept μ ν dst
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J m dst work V : ℕ}
def program : Program := [body 1,LightOutputDecodeDivide.body]
end ThreeSum.LightOutputDecodeDigits


