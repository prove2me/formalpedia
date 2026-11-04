-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
-- name    : Submission_ThreeSum_LightTernarySignedRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:15:37.513237+00:00
-- url     : https://prove2.me/theorems/3fa8cbe5-5cf4-4544-a608-b8e3fc3eac40
-- title:
--   Light Ternary Signed Row
-- statement:
--   Definitions and structural lemmas for Light Ternary Signed Row, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedRow.lean

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_Light_Ends_call
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernarySignedRow
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
def body (pDigits : ℕ) : Stmt :=
  .set 9 (v 0 +' v 1) ;;
  .call pDigits [v 9,v 3,v 4,v 5,v 6] 10 ;;
  pass 11 (v 3) (v 5) (v 2 *' M (v 5 +' v 11)) ;;
  .store (v 5 +' v 3) (v 7) ;;
  .store (v 5 +' v 3 +' k 1) (v 8) ;;
  .set 0 (k 0)
def time (J V : ℕ) : ℕ := LightOutputDecodeDigits.time J V+30*J+150
def word (V radix J : ℕ) : ℕ := LightOutputDecodeDigits.word V radix J
def space (work V : ℕ) : ℕ := LightOutputDecodeDigits.space work V
def Row (μ : ℕ→ℤ) (dst J : ℕ) (f : Coordinate J→ℤ) : Prop :=
  (∀ j : Fin J, μ (dst+J-1-j.val)=f (.inl j)) ∧
    μ (dst+J)=f (.inr false) ∧ μ (dst+J+1)=f (.inr true)
structure Procs (P : Program) (pMain : ℕ) where
  pDigits : ℕ
  pDivide : ℕ
  main : P[pMain]?=some (body pDigits)
  digits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]?=some LightOutputDecodeDivide.body
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightOutputDecodeDigits.body 2,LightOutputDecodeDivide.body]
def procs : Procs program 0 := ⟨1,2,rfl,rfl,rfl⟩
end ThreeSum.LightTernarySignedRow


