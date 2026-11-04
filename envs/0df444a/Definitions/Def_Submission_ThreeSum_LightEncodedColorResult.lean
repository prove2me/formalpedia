-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorResult
-- name    : Submission_ThreeSum_LightEncodedColorResult
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:57:51.011211+00:00
-- url     : https://prove2.me/theorems/e402f461-87cf-47a4-af5a-96a8f3d4ee59
-- title:
--   Light Encoded Color Result
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Result, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorResult.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorSourceRetention
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
namespace ThreeSum.LightEncodedColorResult
open Light
def values (prime cover wanted controls bank out len p : ℕ) : List ℤ :=
  [prime,cover,wanted,controls,bank,out+8,len,p]
def body : Stmt :=
  .set 8 (v 5 +' k 8) ;;
  .store (v 5) (v 0) ;;
  .store (v 5 +' k 1) (v 1) ;;
  .store (v 5 +' k 2) (v 2) ;;
  .store (v 5 +' k 3) (v 3) ;;
  .store (v 5 +' k 4) (v 4) ;;
  .store (v 5 +' k 5) (v 8) ;;
  .store (v 5 +' k 6) (v 6) ;;
  .store (v 5 +' k 7) (v 7) ;;
  .set 0 (v 5)
noncomputable def memory (μ : ℕ → ℤ) (prime cover wanted controls bank out len p : ℕ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update μ out (prime : ℤ))
      (out+1) cover) (out+2) wanted) (out+3) controls) (out+4) bank) (out+5) (out+8)) (out+6) len) (out+7) p
def program : Program := [body]
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightEncodedColorResult


