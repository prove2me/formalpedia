-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
-- name    : Submission_ThreeSum_LightTernaryPredecessorTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:55.614866+00:00
-- url     : https://prove2.me/theorems/19824a2b-3908-428f-860e-572ade295707
-- title:
--   Light Ternary Predecessor Table
-- statement:
--   Definitions and structural lemmas for Light Ternary Predecessor Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
namespace ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
def roundBody (pCell pDigit : ℕ) : Stmt :=
  .set 18 (M (v 3 +' v 17)) ;;
  .call pCell [v 0,v 1,v 2,v 18,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14] 19 ;;
  .call pDigit [k 2 *' v 0,v 1,v 2,v 18,v 5] 20 ;;
  .set 20 (v 14 *' v 20) ;;
  .store (v 15 +' v 16 *' v 17) (v 20) ;;
  .store (v 15 +' v 16 *' v 4 +' v 16 *' v 17) (v 19)
def body (pCell pDigit : ℕ) : Stmt := .for 17 (v 4) (roundBody pCell pDigit)
def time (N L n : ℕ) : ℕ :=
  n*(LightTernaryPredecessor.time N L+LightTernaryCodes.digitTime (2*N)+200)+20
def RecordAt (μ : ℕ → ℤ) (dst stride n j N low high m T active bv nv bi ni : ℕ) : Prop :=
  μ (dst+stride*j)=(weight N low high m active : ℤ) ∧
  μ (dst+stride*n+stride*j)=(key N low high m T active bv nv bi ni : ℤ)
noncomputable def writeRecord (μ : ℕ → ℤ) (dst stride n j : ℕ) (w k : ℤ) : ℕ → ℤ :=
  Function.update (Function.update μ (dst+stride*j) w) (dst+stride*n+stride*j) k
def KeptApart (μ ν : ℕ → ℤ) (dst stride n : ℕ) : Prop :=
  ∀ x, (∀ j<n, x≠dst+stride*j ∧ x≠dst+stride*n+stride*j) → ν x=μ x
def Inv (μ : ℕ → ℤ) (N low high a n powers bank nb bv near nn nv L T active dst stride : ℕ)
    (codes bi ni : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (m k q : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,low,high,a,n,powers,bank,nb,bv,near,nn,nv,L,T,active,dst,stride,j,m,k,q],ν⟩ ∧
    KeptApart μ ν dst stride n ∧
    ∀ l<j, RecordAt ν dst stride n l N low high (codes l) T active bv nv (bi l) (ni l)
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryPredecessorTable


