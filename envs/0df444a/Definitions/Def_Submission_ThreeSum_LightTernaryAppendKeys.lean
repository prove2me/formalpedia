-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
-- name    : Submission_ThreeSum_LightTernaryAppendKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:59.511478+00:00
-- url     : https://prove2.me/theorems/32d43e0d-e449-4b72-b5ec-a02fb0475092
-- title:
--   Light Ternary Append Keys
-- statement:
--   Definitions and structural lemmas for Light Ternary Append Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryAppendKeys.lean

import Definitions.Def_Submission_ThreeSum_LightSignedRowHash
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryAppendKeys
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
def body (pHash : ℕ) : Stmt :=
  .for 9 (v 4) (
    .call pHash [v 0 +' v 9 *' v 5,v 1,v 8,v 5,v 6] 10 ;;
    .store (v 3 +' v 9) (M (v 2 +' v 9) +' v 7 *' v 10))
def key (p power len : ℕ) (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (i : ℕ) : ℕ :=
  old i+power*(LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len%p)
def time (n len p b : ℕ) : ℕ := n*(LightSignedRowHash.time len p b+120)+30
def word (len p b power : ℕ) : ℕ := LightSignedRowHash.word len p b+power*p+100
structure Procs (P : Program) (main : ℕ) where
  hash : ℕ
  mainBody : P[main]?=some (body hash)
  hashProcs : LightSignedRowHash.Procs P hash
def Inv (μ : ℕ → ℤ) (matrix row oldBase dst n len p power scratch : ℕ)
    (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (val : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [matrix,row,oldBase,dst,n,len,p,power,scratch,i,val],ν⟩ ∧
    (∀ j<i, ν (dst+j)=(key p power len old z c j : ℤ)) ∧ Kept μ ν dst
variable {lim : Limits} {P : Program} {depth : ℕ}
def program : Program := LightSignedRowHash.program++[body 0]
def procs : Procs program 6 where
  hash := 0
  mainBody := rfl
  hashProcs := {
    lift := 1,dot := 2,rawDot := 3,digit := 4,divide := 5,
    mainBody := rfl,liftBody := rfl,dotBody := rfl,rawBody := rfl,
    digitBody := rfl,divideBody := rfl }
end ThreeSum.LightTernaryAppendKeys


