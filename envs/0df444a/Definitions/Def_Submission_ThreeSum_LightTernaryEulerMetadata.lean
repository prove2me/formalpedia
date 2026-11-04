-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
-- name    : Submission_ThreeSum_LightTernaryEulerMetadata
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:51:06.993739+00:00
-- url     : https://prove2.me/theorems/00b3588b-5b60-474e-8f39-e2667a880520
-- title:
--   Light Ternary Euler Metadata
-- statement:
--   Definitions and structural lemmas for Light Ternary Euler Metadata, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
def lowAt (N i : ℕ) : ℕ := 2*(N-1-i)
def highAt (N i : ℕ) : ℕ := lowAt N i+1
def rowAddr (ws N i j : ℕ) : ℕ := ws+N*j+i
def RecordAt (μ : ℕ → ℤ) (N rows ws i j m T active bv nv bi ni : ℕ) : Prop :=
  μ (rowAddr ws N i j)=(weight N (lowAt N i) (highAt N i) m active : ℤ) ∧
  μ (rowAddr ws N i (rows+j))=(key N (lowAt N i) (highAt N i) m T active bv nv bi ni : ℤ)
def roundBody (pColumn : ℕ) : Stmt :=
  .set 15 (k 2 *' (v 0 -' k 1 -' v 14)) ;;
  .set 16 (v 15 +' k 1) ;;
  .set 17 (M (v 12 +' v 14)) ;;
  .call pColumn [v 0,v 15,v 16,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,
    v 17,v 13 +' v 14,v 0] 18
def body (pColumn : ℕ) : Stmt := .for 14 (v 0) (roundBody pColumn)
def time (N L rows : ℕ) : ℕ := N*(LightTernaryPredecessorTable.time N L rows+200)+20
def Inv (μ : ℕ → ℤ) (N a rows powers bank nb bv near nn nv L T activeBase ws : ℕ)
    (codes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (lo hi act result : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,a,rows,powers,bank,nb,bv,near,nn,nv,L,T,activeBase,ws,i,lo,hi,act,result],ν⟩ ∧
    SameOutside μ ν ws (2*N*rows) ∧
    ∀ k < i, ∀ j<rows, RecordAt ν N rows ws k j (codes j) T (active k) bv nv (bi k j) (ni k j)
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryEulerMetadata


