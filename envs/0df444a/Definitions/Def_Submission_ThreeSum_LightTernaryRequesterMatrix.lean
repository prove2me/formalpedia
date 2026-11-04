-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
-- name    : Submission_ThreeSum_LightTernaryRequesterMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:26:17.900814+00:00
-- url     : https://prove2.me/theorems/6a1af0a4-9c58-4a61-b667-21d815fc3cce
-- title:
--   Light Ternary Requester Matrix
-- statement:
--   Definitions and structural lemmas for Light Ternary Requester Matrix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
def round (pRequester : ℕ) : Stmt :=
  .store (v 6 +' v 9 *' v 5 +' v 10) (v 9) ;;
  .call pRequester [M (v 0 +' v 9),v 1,v 3,v 2,
    v 7 +' (v 9 *' v 5 +' v 10) *' (v 2 +' k 2),
    v 4 +' v 10 *' (v 2 +' k 1),v 8] 11
def innerBody (pRequester : ℕ) : Stmt := .for 10 (v 5) (round pRequester)
def body (pInner : ℕ) : Stmt :=
  .for 10 (v 1) (.call pInner [v 0,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10] 11)
def innerTime (Q J U : ℕ) : ℕ := Q*(LightTernaryOriginalRequester.time J U+300)+30
def time (n Q J U : ℕ) : ℕ := n*(innerTime Q J U+200)+30
def Entries (μ : ℕ → ℤ) (positions matrix J Q len U radix : ℕ) (f : ℕ → ℤ) : Prop :=
  ∀ r<len,
    LightTernarySignedRow.Row μ (matrix+r*(J+2)) J
      (requesterRaw U radix J (f (r/Q)) (TernaryCarryCode.carryFromCode J (r%Q))) ∧
    μ (positions+r)=(r/Q : ℕ)
structure Procs (P : Program) (main : ℕ) where
  inner : ℕ
  requester : ℕ
  mainBody : P[main]?=some (body inner)
  innerBody : P[inner]?=some (innerBody requester)
  requesterProcs : LightTernaryOriginalRequester.Procs P requester
variable {lim : Limits} {P : Program} {depth : ℕ}
def InnerInv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (src U J radix carry Q positions matrix work i j : ℕ) (σ : State) : Prop :=
  ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [src,U,J,radix,carry,Q,positions,matrix,work,i,j,result],ν⟩ ∧
    Entries ν positions matrix J Q (i*Q+j) U radix f ∧ Kept μ ν positions
def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (src n U J radix carry Q positions matrix work i : ℕ) (σ : State) : Prop :=
  ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [src,n,U,J,radix,carry,Q,positions,matrix,work,i,result],ν⟩ ∧
    Entries ν positions matrix J Q (i*Q) U radix f ∧ Kept μ ν positions
def program : Program := LightTernaryOriginalRequester.program++[innerBody 0,body 6]
def procs : Procs program 7 where
  inner := 6
  requester := 0
  mainBody := rfl
  innerBody := rfl
  requesterProcs := {
    pRow := 1,pApply := 4,pLinear := 5,
    row := ⟨2,3,rfl,rfl,rfl⟩,
    correction := rfl,linear := rfl,main := rfl }
def value (U radix J Q : ℕ) (f : ℕ → ℤ) (row coordinate : ℕ) : ℤ :=
  TernarySignedLayout.feature
    (requesterRaw U radix J (f (row/Q)) (TernaryCarryCode.carryFromCode J (row%Q)))
    (TernarySignedLayout.offset J coordinate)
end ThreeSum.LightTernaryRequesterMatrix


