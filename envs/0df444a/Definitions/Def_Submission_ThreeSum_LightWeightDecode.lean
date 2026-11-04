-- Prove2me | Definitions.Def_Submission_ThreeSum_LightWeightDecode
-- name    : Submission_ThreeSum_LightWeightDecode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:55:36.161342+00:00
-- url     : https://prove2.me/theorems/90cf3007-7e79-4418-9148-d2adce8d5749
-- title:
--   Light Weight Decode
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightDecode.lean

import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightWeightDecode
open Light
def body (pPowers pRow : ℕ) : Stmt :=
  .set 5 (k 2 *' v 0) ;;
  .call pPowers [v 4,v 5 +' k 1,v 1] 6 ;;
  .call pRow [v 5,v 1,v 2,v 4,k 0,k 2,v 3,v 0] 6 ;;
  .call pRow [v 5,v 1,v 2,v 4,k 1,k 2,v 3 +' v 0,v 0] 6
def time (L k : ℕ) : ℕ := powTableTime (2*L+1)+2*LightWeightRow.time L k+120
def word (L p k : ℕ) : ℕ := LightWeightRow.word (2*L) p k 1 2
def Rows (μ : ℕ → ℤ) (dst L p k : ℕ) : Prop :=
  ∀ i < L,
    μ (dst+i) = (WeightEnumeration.digit p (2*L) k (2*i) : ℤ) ∧
    μ (dst+L+i) = (WeightEnumeration.digit p (2*L) k (2*i+1) : ℤ)
structure Procs (P : Program) (pMain : ℕ) where
  pPowers : ℕ
  pRow : ℕ
  pDigit : ℕ
  pDivide : ℕ
  powers : P[pPowers]? = some powTableBody
  row : P[pRow]? = some (LightWeightRow.body pDigit)
  digit : P[pDigit]? = some (LightRadixDigit.body pDivide)
  divide : P[pDivide]? = some LightSmallDivide.body
  main : P[pMain]? = some (body pPowers pRow)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 2,powTableBody,LightWeightRow.body 3,LightRadixDigit.body 4,LightSmallDivide.body]
def programProcs : Procs program 0 := ⟨1,2,3,4,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightWeightDecode


