-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceResidues
-- name    : Submission_ThreeSum_LightSourceResidues
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:19.774251+00:00
-- url     : https://prove2.me/theorems/2e65d886-a747-4fab-bc0e-082bf99d20e6
-- title:
--   Light Source Residues
-- statement:
--   Definitions and structural lemmas for Light Source Residues, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean

import Definitions.Def_Submission_ThreeSum_LightResidues
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
def key (p m : ℕ) (shift x : ℤ) : ℕ := ((x % (p : ℤ) + shift) % (m : ℤ)).toNat
def body (pEmod : ℕ) : Stmt :=
  .for 7 (v 2) (
    .call pEmod [M (v 0 +' v 7),v 3,v 5] 8 ;;
    .call pEmod [v 8 +' v 6,v 4,v 5] 9 ;;
    .store (v 1 +' v 7) (v 9))
def time (n p U D : ℕ) : ℕ :=
  n * (LightResidues.residueBudget U + LightResidues.residueBudget (p+D) + 100) + 6
def word (p m U D : ℕ) : ℕ := 4*U+8*p+4*D+4*m+32
def space (work p U D : ℕ) : ℕ :=
  work + max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)
def Inv (μ : ℕ → ℤ) (src dst n p m work : ℕ) (shift : ℤ) (i : ℕ)
    (σ : State) : Prop :=
  ∃ (r0 r1 : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [src,dst,n,p,m,work,shift,i,r0,r1],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (key p m shift (μ (src+j)) : ℤ)) ∧
    KeptBut μ ν work dst n
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,emodBody]
end ThreeSum.LightSourceResidues


