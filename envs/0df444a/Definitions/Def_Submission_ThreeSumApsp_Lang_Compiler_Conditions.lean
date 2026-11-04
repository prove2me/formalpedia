-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
-- name    : Submission_ThreeSumApsp_Lang_Compiler_Conditions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:11:38.587446+00:00
-- url     : https://prove2.me/theorems/63765806-4d20-4079-bf3a-7ac69a9383a0
-- title:
--   Conditions
-- statement:
--   Definitions and structural lemmas for Conditions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}
def Decides (code : List Instr) (F pos size l : ℕ) (m : ℤ → BitVec W) (p : Prop) : Prop :=
  ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
    (p → Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩) ∧ (¬ p → Steps code n ⟨pos, m⟩ ⟨l, m'⟩)
end Light.Compiler


