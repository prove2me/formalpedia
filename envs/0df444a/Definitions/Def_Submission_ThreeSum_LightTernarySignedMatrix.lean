-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
-- name    : Submission_ThreeSum_LightTernarySignedMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:18:57.910592+00:00
-- url     : https://prove2.me/theorems/10fbc3b7-bbaa-40b2-8329-3c13f1eb6d66
-- title:
--   Light Ternary Signed Matrix
-- statement:
--   Definitions and structural lemmas for Light Ternary Signed Matrix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedMatrix.lean

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightTernarySignedMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
def raw (right : Bool) (U radix J : ℕ) (x : ℤ) : Coordinate J → ℤ :=
  if right then rightRaw U radix J x else leftRaw U radix J x
def body (right : Bool) (pRow : ℕ) : Stmt :=
  .for 7 (v 1) (
    .call pRow [M (v 0 +' v 7),
      (if right then k 2 *' v 2 else v 2),
      (if right then k 1 else k 0 -' k 1),v 3,v 4,
      v 5 +' v 7 *' (v 3 +' k 2),v 6,
      k (if right then 0 else 1),k (if right then 1 else 0)] 8)
def time (n J U : ℕ) : ℕ := n*(LightTernarySignedRow.time J (3*U)+200)+20
def word (U radix J : ℕ) : ℕ := LightTernarySignedRow.word (3*U) radix J
def space (work U : ℕ) : ℕ := LightTernarySignedRow.space work (3*U)
def Rows (μ : ℕ → ℤ) (dst n J : ℕ) (f : ℕ → Coordinate J → ℤ) : Prop :=
  ∀ i < n, LightTernarySignedRow.Row μ (dst+i*(J+2)) J (f i)
structure Procs (P : Program) (pMain : ℕ) (right : Bool) where
  pRow : ℕ
  row : LightTernarySignedRow.Procs P pRow
  main : P[pMain]? = some (body right pRow)
def Inv (right : Bool) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (src n U J radix dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [src,n,U,J,radix,dst,work,i,r],ν⟩ ∧
    Rows ν dst i J (fun j => raw right U radix J (f j)) ∧ Kept μ ν dst
variable {lim : Limits} {P : Program} {d : ℕ}
def program (right : Bool) : Program :=
  [body right 1,LightTernarySignedRow.body 2,LightOutputDecodeDigits.body 3,
    LightOutputDecodeDivide.body]
def procs (right : Bool) : Procs (program right) 0 right :=
  ⟨1,⟨2,3,rfl,rfl,rfl⟩,rfl⟩
end ThreeSum.LightTernarySignedMatrix


