-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPrimePool
-- name    : Submission_ThreeSum_LightPrimePool
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:40.094192+00:00
-- url     : https://prove2.me/theorems/21292e3c-48ba-42f7-94ac-adba9383013f
-- title:
--   Light Prime Pool
-- statement:
--   Definitions and structural lemmas for Light Prime Pool, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def scanned (y : ℕ) : ℕ → List ℕ
  | 0 => []
  | i+1 =>
    if Nat.Prime (y+i+1) then scanned y i ++ [y+i+1] else scanned y i
def values (y : ℕ) : List ℕ := scanned y (3*y)
def size (y : ℕ) : ℕ := (values y).length
def prime (y i : ℕ) : ℕ := (values y).getD i 0
def body (pTest : ℕ) : Stmt :=
  .set 2 (k 0) ;;
  .set 6 (v 1 +' k 3 *' v 0) ;;
  .for 3 (k 3 *' v 0) (
    .set 4 (v 0 +' v 3 +' k 1) ;;
    .call pTest [v 4,v 6] 5 ;;
    .ite (v 5 =' k 1) (
      .store (v 1 +' v 2) (v 4) ;;
      .set 2 (v 2 +' k 1)) .skip) ;;
  .set 0 (v 2)
def time (y : ℕ) : ℕ := 3*y*(LightPrimality.time (4*y) (4*y)+100)+100
def space (free y : ℕ) : ℕ := free+3*y+(Nat.log 2 (4*y+1)+2)
def word (y : ℕ) : ℕ := 32*y+16
def Inv (μ : ℕ → ℤ) (y free i : ℕ) (σ : State) : Prop :=
  ∃ (cval rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(y : ℤ),free,(scanned y i).length,i,cval,rval,free+3*y],ν⟩ ∧
      SegN ν free (scanned y i) ∧ Kept μ ν free
structure Procs (P : Program) (pMain : ℕ) where
  pTest : ℕ
  test : LightPrimality.Procs P pTest
  main : P[pMain]? = some (body pTest)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightPrimality.body 2,emodBody]
def program_procs : Procs program 0 where
  pTest := 1
  test := ⟨2,rfl,rfl⟩
  main := rfl
end ThreeSum.LightPrimePool


