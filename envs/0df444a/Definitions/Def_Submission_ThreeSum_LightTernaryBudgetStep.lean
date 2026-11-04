-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
-- name    : Submission_ThreeSum_LightTernaryBudgetStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:38.447593+00:00
-- url     : https://prove2.me/theorems/86951d67-ce64-4763-b0f1-e0242914829c
-- title:
--   Light Ternary Budget Step
-- statement:
--   Definitions and structural lemmas for Light Ternary Budget Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBudgetStep.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
namespace ThreeSum.LightTernaryBudgetStep
open Light
set_option maxHeartbeats 3000000
def body : Stmt :=
  .set 5 (M (v 0) *' v 1) ;;
  .set 6 (M (v 0 +' k 1) *' v 1) ;;
  .set 7 (M (v 0 +' k 2) *' v 2) ;;
  .set 8 (M (v 0 +' k 3) *' k 9) ;;
  .set 9 (M (v 0 +' k 4) *' k 9) ;;
  .set 10 (M (v 0 +' k 5) *' v 3 *' v 4) ;;
  .store (v 0) (v 5) ;;
  .store (v 0 +' k 1) (v 6) ;;
  .store (v 0 +' k 2) (v 7) ;;
  .store (v 0 +' k 3) (v 8) ;;
  .store (v 0 +' k 4) (v 9) ;;
  .store (v 0 +' k 5) (v 10) ;;
  .set 0 (k 0)
def oldValues (xB xC xP tB tC tP : ℕ) : List ℤ := [xB,xC,xP,tB,tC,tP]
def nextValues (p a b s xB xC xP tB tC tP : ℕ) : List ℤ :=
  [xB*p,xC*p,xP*a,tB*9,tC*9,tP*b*s]
noncomputable def changed (μ : ℕ→ ℤ) (base p a b s xB xC xP tB tC tP : ℕ) : ℕ→ ℤ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update μ base (xB*p)) (base+1) (xC*p))
      (base+2) (xP*a)) (base+3) (tB*9)) (base+4) (tC*9)) (base+5) (tP*b*s)
end ThreeSum.LightTernaryBudgetStep


