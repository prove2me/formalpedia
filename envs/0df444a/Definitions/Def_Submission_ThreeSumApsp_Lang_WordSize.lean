-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
-- name    : Submission_ThreeSumApsp_Lang_WordSize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:57:36.528503+00:00
-- url     : https://prove2.me/theorems/3678fe4d-faa7-46bd-9624-693ca6bc6d60
-- title:
--   Word Size
-- statement:
--   Supporting definitions from the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
namespace Light
open ThreeSumApsp.WordRam
def polyBound (s k : ℕ) (params : List ℕ) : ℕ := 2 ^ s * ((params.map (· + 1)).prod) ^ k
end Light


