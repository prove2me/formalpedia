-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPrimality
-- name    : Submission_ThreeSum_LightPrimality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:03.503586+00:00
-- url     : https://prove2.me/theorems/1d36086f-ebef-42bb-88f8-0dce2c2cb765
-- title:
--   Light Primality
-- statement:
--   Definitions and structural lemmas for Light Primality, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def flag (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => if i+2 ∣ n then 0 else flag n i
def answer (n : ℕ) : ℕ := if Nat.Prime n then 1 else 0
def body (pEmod : ℕ) : Stmt :=
  .set 2 (k 1) ;;
  .for 3 (v 0 -' k 2) (
    .call pEmod [v 0,v 3 +' k 2,v 1] 4 ;;
    .ite (v 4 =' k 0) (.set 2 (k 0)) .skip) ;;
  .set 0 (v 2)
def time (n maxValue : ℕ) : ℕ := (n-2)*(residueBudget maxValue+70)+70
def Inv (μ : ℕ → ℤ) (n free i : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(n : ℤ),free,flag n i,i,rval],ν⟩ ∧ Kept μ ν free
variable {lim : Limits} {P : Program} {d : ℕ}
structure Procs (P : Program) (pMain : ℕ) where
  pEmod : ℕ
  main : P[pMain]? = some (body pEmod)
  emod : P[pEmod]? = some emodBody
def program : Program := [body 1,emodBody]
def program_procs : Procs program 0 where
  pEmod := 1
  main := rfl
  emod := rfl
end ThreeSum.LightPrimality


