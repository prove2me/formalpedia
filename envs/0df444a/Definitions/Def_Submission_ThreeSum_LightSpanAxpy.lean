-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSpanAxpy
-- name    : Submission_ThreeSum_LightSpanAxpy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:57.619212+00:00
-- url     : https://prove2.me/theorems/1ad64e4a-2a65-446e-9efc-ec5963ea47f6
-- title:
--   Light Span Axpy
-- statement:
--   Definitions and structural lemmas for Light Span Axpy, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanAxpy.lean

import Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSpanAxpy
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
def roundBody (pMulAdd : ℕ) : Stmt :=
  .set 7 (M (v 0 +' v 6)) ;;
  .set 8 (M (v 1 +' v 6)) ;;
  .call pMulAdd [v 7,v 4,v 8,v 5] 9 ;;
  .store (v 2 +' v 6) (v 9)
def body (pMulAdd : ℕ) : Stmt := .for 6 (v 3) (roundBody pMulAdd)
def time (J p : ℕ) : ℕ := J*(LightPrimeCoefficient.mulAddTime p+150)+20
def values (f row : ℕ → ℕ) (a p i : ℕ) : ℤ := ((f i+a*row i)%p : ℕ)
def Inv (μ : ℕ → ℤ) (src rowBase dst J a p : ℕ) (f row : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ x y z : ℤ, σ=⟨frame [src,rowBase,dst,J,a,p,j,x,y,z],wrote μ dst (values f row a p) j⟩
variable {lim : Limits} {P : Program}
end ThreeSum.LightSpanAxpy


