-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
-- name    : Submission_ThreeSum_LightTernaryInitialBudgets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:00.780206+00:00
-- url     : https://prove2.me/theorems/38e116fa-60bb-43b3-bbb6-f4e5e98f3adb
-- title:
--   Light Ternary Initial Budgets
-- statement:
--   Definitions and structural lemmas for Light Ternary Initial Budgets, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInitialBudgets.lean

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryInitialBudgets
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
def determinantBound (K bDigit : ℕ) : ℕ :=(2*K).factorial*bDigit^(2*K)
def initial (K bDigit n J nO : ℕ) : ℕ :=
  nO*n^(2*K)*(J+2)^(2*K)*(determinantBound K bDigit)^2
def body (K bDigit a b scaleBase : ℕ) : Stmt :=
  .call 0 [v 0,k (2*K)] 5 ;;
  .call 0 [v 1 +' k 2,k (2*K)] 6 ;;
  .set 7 (v 2 *' v 5 *' v 6 *' k ((determinantBound K bDigit)^2)) ;;
  .set 8 (v 0 *' v 0) ;;
  .store (v 3 +' k 41) (k 1) ;;
  .store (v 3 +' k 42) (k 1) ;;
  .store (v 3 +' k 43) (k 1) ;;
  .store (v 3 +' k 44) (v 8) ;;
  .store (v 3 +' k 45) (v 8) ;;
  .store (v 3 +' k 46) (v 7) ;;
  .store (v 4) (k a) ;;
  .store (v 4 +' k 1) (k b) ;;
  .store (v 4 +' k 2) (k scaleBase) ;;
  .set 0 (v 7)
def program (K bDigit a b scaleBase : ℕ) : Program :=
  LightNatPower.program++[body K bDigit a b scaleBase]
def time (K : ℕ) : ℕ :=2*LightNatPower.time (2*K)+1000
def word (K bDigit a b scaleBase n J nO : ℕ) : ℕ :=
  initial K bDigit n J nO+n*n+n+J+2+nO+n^(2*K)+(J+2)^(2*K)+
    (determinantBound K bDigit)^2+a+b+scaleBase+2*K+100
end ThreeSum.LightTernaryInitialBudgets


