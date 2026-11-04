-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
-- name    : Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:07:45.432495+00:00
-- url     : https://prove2.me/theorems/c71b6b0c-41f7-4690-89f6-bd544f8d1786
-- title:
--   Dispatcher
-- statement:
--   Definitions and structural lemmas for Dispatcher, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Dispatcher.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
@[expose] section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {code : List Instr} {disp n : ℕ}
end Light.Compiler


