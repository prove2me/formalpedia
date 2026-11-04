-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
-- name    : Submission_ThreeSumApsp_Lang_Compiler_StartUp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:15:17.618395+00:00
-- url     : https://prove2.me/theorems/b65bdc4c-0904-47f6-b902-9f8c9bcd0de2
-- title:
--   Start Up
-- statement:
--   Definitions and structural lemmas for Start Up, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}
def poolMem (N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (poolCode N) (effects headStraight m)
def startMem (F N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (startStraight F N) (effects headStraight m)
end Light.Compiler


