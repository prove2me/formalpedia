-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
-- name    : Submission_ThreeSumApsp_Statements_Exponents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:58:17.67605+00:00
-- url     : https://prove2.me/theorems/6ec46463-22b0-41d6-82b2-87c6f74f6f85
-- title:
--   Exponents
-- statement:
--   Definitions and structural lemmas for Exponents, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
set_option autoImplicit false
section
@[expose] section
namespace ThreeSumApsp.WordRam
noncomputable def stepBound (C a : ℝ) (n : ℕ) : ℕ := ⌈C * ((n : ℝ) ^ a + 1)⌉₊
end ThreeSumApsp.WordRam


