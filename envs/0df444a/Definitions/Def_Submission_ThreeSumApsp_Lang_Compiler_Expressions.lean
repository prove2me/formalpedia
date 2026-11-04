-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
-- name    : Submission_ThreeSumApsp_Lang_Compiler_Expressions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:07:55.419894+00:00
-- url     : https://prove2.me/theorems/40900cf9-3b6f-4755-a5ce-853a8d32b9aa
-- title:
--   Expressions
-- statement:
--   Definitions and structural lemmas for Expressions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Expressions.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
@[expose] section
open ThreeSumApsp.WordRam
namespace Light.Compiler
variable {W : ℕ} {F : ℕ}
variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
end Light.Compiler


