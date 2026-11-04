-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
-- name    : Submission_ThreeSumApsp_Machine_Realized
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:01:15.050172+00:00
-- url     : https://prove2.me/theorems/d10bac7e-3594-4f98-81ac-3b1ea5aead7d
-- title:
--   Realized
-- statement:
--   Definitions and structural lemmas for Realized, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Realized.lean

import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
set_option autoImplicit false
section
open EndStatement (Instr)
namespace ThreeSumApsp.WordRam
def RealizedWithin (prob : Problem) (size bound : prob.Inst → ℕ) (dom : prob.Inst → Prop)
    (T : prob.Inst → ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List Instr) (b : ℕ) (c : ℝ), 0 ≤ c ∧
    Solves prob P b (fun x => dom x ∧ 1 ≤ size x ∧ bound x = size x ^ κ) (fun x => c * T x + c)
def Realized (Q : EndStatement.Problem) (T : ℕ → ℝ → ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List Instr) (b : ℕ) (c : ℝ), 0 ≤ c ∧
    Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ) (fun x => c * max (T x.n x.U) 0 + c)
end ThreeSumApsp.WordRam


