-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceGather
-- name    : Submission_ThreeSum_LightSourceGather
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:58.138472+00:00
-- url     : https://prove2.me/theorems/e3c4e211-2249-4e06-a185-fc08b86b2dcf
-- title:
--   Light Source Gather
-- statement:
--   Definitions and structural lemmas for Light Source Gather, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceGather.lean

import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceGather
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
def value (m : ℕ) (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ) (i : ℕ) : ℕ :=
  if flag i = 1 then hist (LightResidues.residue m 1 (endpoint i)) else 0
def body (pEmod : ℕ) : Stmt :=
  .for 7 (v 4) (
    .call pEmod [M (v 0 +' v 7),v 5,v 6] 8 ;;
    .ite (M (v 1 +' v 7) =' k 1)
      (.store (v 3 +' v 7) (M (v 2 +' v 8)))
      (.store (v 3 +' v 7) (k 0)))
def time (n U : ℕ) : ℕ := n*(LightResidues.residueBudget U+80)+6
def Inv (μ : ℕ → ℤ) (raw flags table dst n m work : ℕ)
    (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ), σ = ⟨frame [raw,flags,table,dst,n,m,work,i,r],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (value m endpoint flag hist j : ℤ)) ∧
    KeptBut μ ν work dst n
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,emodBody]
end ThreeSum.LightSourceGather


