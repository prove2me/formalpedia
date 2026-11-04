-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
-- name    : Submission_ThreeSum_LightTernaryCarryCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:15:32.302321+00:00
-- url     : https://prove2.me/theorems/2419b588-56d6-4070-8092-9a30b411a123
-- title:
--   Light Ternary Carry Codes
-- statement:
--   Definitions and structural lemmas for Light Ternary Carry Codes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
def initial (J q : ℕ) : ℕ := if J=0 then 0 else digit 2 q 0
def accepted (J q : ℕ) : ℕ := if initial J q=0 then 1 else 0
def Row (ν : ℕ → ℤ) (dst J q : ℕ) : Prop :=
  ν dst=0 ∧
  (∀ j<J, ν (dst+J-j)=(digit 2 q j : ℤ))
def rowBody (pDecode : ℕ) : Stmt :=
  .call pDecode [v 0,v 1,k 2,v 2 +' k 1,v 3] 4 ;;
  .store (v 2) (k 0) ;;
  .ite (M (v 2 +' v 1) =' k 0)
    (.set 0 (k 1))
    (.set 0 (k 0))
def rowTime (J V : ℕ) : ℕ := LightOutputDecodeDigits.time J V+100
def word (J V : ℕ) : ℕ := LightOutputDecodeDigits.word V 2 J+100
def space (work V : ℕ) : ℕ := LightOutputDecodeDigits.space work V
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
def tableBody (pRow : ℕ) : Stmt :=
  .for 4 (v 0)
    (.call pRow [v 4,v 1,v 2 +' v 4 *' (v 1 +' k 1),v 3] 5) ;;
  .set 0 (v 0)
def tableTime (Q J : ℕ) : ℕ := Q*(rowTime J Q+100)+30
def Table (ν : ℕ → ℤ) (dst J Q : ℕ) : Prop :=
  ∀ q<Q, Row ν (dst+q*(J+1)) J q
def TableInv (μ : ℕ → ℤ) (Q J dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [Q,J,dst,work,i,r],ν⟩ ∧ Table ν dst J i ∧ Kept μ ν dst
def body (pPower pTable : ℕ) : Stmt :=
  .call pPower [k 2,v 0] 3 ;;
  .call pTable [v 3,v 0,v 1,v 2] 4 ;;
  .set 0 (v 3)
def time (J : ℕ) : ℕ :=
  LightNatPower.time J+tableTime (2^J) J+100
def program : Program :=
  [body 1 2,LightNatPower.body,tableBody 3,rowBody 4,
    LightOutputDecodeDigits.body 5,LightOutputDecodeDivide.body]
end ThreeSum.LightTernaryCarryCodes


