-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
-- name    : Submission_ThreeSumApsp_Lang_TopProcedure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:25:39.508585+00:00
-- url     : https://prove2.me/theorems/6ad44635-3d49-4b9a-bae5-f8450d607952
-- title:
--   Top Procedure
-- statement:
--   Definitions and structural lemmas for Top Procedure, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
section
namespace Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}
def powStmt : ℕ → Stmt
  | 0 => .skip
  | κ + 1 => powStmt κ ;; .set 2 (v 2 *' v 1)
def topBody (κ p : ℕ) (args : List Expr) (dec : Bool) : Stmt :=
  .set 1 (M (k 0)) ;;
  Stmt.iteNe (v 1) (k 0)
    (.set 2 (k 1) ;;
    powStmt κ ;;
    .set 3 (v 1 *' v 1) ;;
    .call p args 0 ;;
    (if dec then .skip else .set 0 (k 1)))
    (.set 0 (k (if dec then 0 else 1)))
section OfEnd
variable {Q : EndStatement.Problem} (x : Bounded Q)
end OfEnd
structure Wrap (Q : EndStatement.Problem) (task : Task) (dec : Bool) where
  /-- The input and the output take at most cst (n² + 1) cells. -/
  cst : ℕ := 8
  cst_pos : 1 ≤ cst := by omega
  /-- The arguments of the solver, the free pointer last, as expressions in the locals 1 (n), 2 (U)
  and 3 (n²). -/
  args : List Expr
  /-- The instance of the task. -/
  inst : Bounded Q → task.Inst
  /-- The free pointer: the first cell after the output. -/
  fr : Bounded Q → ℕ
  size_eq : ∀ x : Bounded Q, task.size (inst x) = x.n
  bound_eq : ∀ x : Bounded Q, task.bound (inst x) = x.U
  fr_pos : ∀ x : Bounded Q, 1 ≤ fr x
  fr_le : ∀ x : Bounded Q, fr x ≤ cst * (x.n * x.n + 1)
  /-- The expressions have the values that the solver expects. -/
  vals : ∀ (x : Bounded Q) (σ : State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → args.map (·.val σ) = task.args (inst x) ++ [(fr x : ℤ)]
  /-- They may be evaluated as soon as the addresses of the input and the output fit in a word. -/
  safe : ∀ (x : Bounded Q) (lim : Limits) (σ : State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → ((cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ e ∈ args, e.Safe lim σ
  /-- At size 0 it is right to reject, for a decision problem, and to accept, whatever the output
  cells hold, for a problem with an output. -/
  zero : ∀ x : Bounded Q, x.n = 0 → ∀ out, (ofEnd Q).IsAnswer x (!dec) out
  /-- The input meets the precondition of the task. -/
  pre : ∀ x : Bounded Q, 1 ≤ x.n → 1 ≤ x.U →
    task.Pre (inst x) (memOf ((ofEnd Q).input x)) (fr x)
  /-- What the task promises is a right answer. -/
  post : ∀ (x : Bounded Q) r μ', 1 ≤ x.n →
    task.Post (inst x) (memOf ((ofEnd Q).input x)) (fr x) r μ' →
    (ofEnd Q).IsAnswer x (verdictOf dec (if dec then r else 1)) fun i =>
      μ' (((ofEnd Q).input x).length + i)
namespace Wrap
variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}
def bodySteps (w : Wrap Q task dec) (κ : ℕ) : ℕ := 4 * κ + (w.args.map Expr.cost).sum + 20
def extra (w : Wrap Q task dec) (κ : ℕ) : ℕ := w.bodySteps κ + 4
def limits (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) : Limits :=
  { word := ((need x.n x.U).word + (w.fr x + (need x.n x.U).cells) + w.cst * (x.n * x.n + 1) +
      x.U + x.n + 1 : ℕ)
    space := w.fr x + (need x.n x.U).cells
    depth := (need x.n x.U).depth + 2 }
structure Room (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) (lim : Limits) :
    Prop where
  /-- The addresses of the input and the output fit in a word. -/
  cells : ((w.cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word
  /-- The bound on the numbers, and 1, fit in a word. -/
  bound : ((x.U + 1 : ℕ) : ℤ) ≤ lim.word
  space : 1 ≤ lim.space
  depth : 2 ≤ lim.depth
  /-- The solver, called at depth 2 with the free pointer behind the output, has what it needs. -/
  solver : (need x.n x.U).Ok lim (w.fr x) 2
abbrev Answered (x : Bounded Q) (dec : Bool) (σ : State) : Prop :=
  (ofEnd Q).IsAnswer x (verdictOf dec (σ.loc 0)) fun i => σ.mem (((ofEnd Q).input x).length + i)
end Wrap
end Light


