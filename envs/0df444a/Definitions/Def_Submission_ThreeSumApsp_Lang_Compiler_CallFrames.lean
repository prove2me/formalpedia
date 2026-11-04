-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
-- name    : Submission_ThreeSumApsp_Lang_Compiler_CallFrames
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:15:08.445315+00:00
-- url     : https://prove2.me/theorems/75cf4e60-0c2a-40b2-9082-7f33a5ef7613
-- title:
--   Call Frames
-- statement:
--   Definitions and structural lemmas for Call Frames, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
set_option autoImplicit false
section
@[expose] section
open ThreeSumApsp.WordRam
namespace Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
end Light.Compiler


