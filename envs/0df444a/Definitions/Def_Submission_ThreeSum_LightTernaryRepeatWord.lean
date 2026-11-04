-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
-- name    : Submission_ThreeSum_LightTernaryRepeatWord
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:53:25.090687+00:00
-- url     : https://prove2.me/theorems/4fd593ae-d62f-4806-8f2a-6d523713070d
-- title:
--   Light Ternary Repeat Word
-- statement:
--   Definitions and structural lemmas for Light Ternary Repeat Word, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRepeatWord.lean

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryRepeatWord
open Light
set_option maxHeartbeats 2000000
def value (q b : ℕ) : ℕ→ ℕ
  | 0=>0
  | i+1=>value q b i*b+q
def body : Stmt :=
  .set 3 (k 0) ;;
  .for 4 (v 2) (.set 3 (v 3 *' v 1 +' v 0)) ;;
  .set 0 (v 3)
def time (s : ℕ) : ℕ := 30*s+30
end ThreeSum.LightTernaryRepeatWord


