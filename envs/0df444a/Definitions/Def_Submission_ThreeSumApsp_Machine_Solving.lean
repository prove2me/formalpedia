-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
-- name    : Submission_ThreeSumApsp_Machine_Solving
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:57:39.937286+00:00
-- url     : https://prove2.me/theorems/cf4ccd6c-8d9d-48a1-b44f-b8eaf10bb74c
-- title:
--   Solving
-- statement:
--   Supporting definitions from the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
set_option autoImplicit false
section
@[expose] section
namespace ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter
structure Bounded (Q : EndStatement.Problem) where
  /-- The size. -/
  n : ℕ
  /-- The bound on the absolute values of the numbers of the input. -/
  U : ℕ
  /-- The instance. -/
  x : Q.Instance n
  /-- The numbers are bounded. -/
  bounded : ∀ a ∈ Q.input x, a.natAbs ≤ U
abbrev ofEnd (Q : EndStatement.Problem) : Problem where
  Inst := Bounded Q
  params x := [x.n]
  input x := (x.n : ℤ) :: Q.input x.x
  IsAnswer x verdict out := (verdict = true ↔ Q.yes x.x) ∧ Q.output x.x out
end ThreeSumApsp.WordRam


