-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Simulation
-- name    : Submission_ThreeSumApsp_Lang_Compiler_Simulation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:19:12.667522+00:00
-- url     : https://prove2.me/theorems/6ddb2ac5-aa32-4522-8afb-75cda2da0b02
-- title:
--   Simulation
-- statement:
--   Definitions and structural lemmas for Simulation, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Simulation.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_WeightedCache3SUM_Alias_e0bdc711e9667f3c

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
section layout
variable {code : List Instr} {G : CodeLayout} {pos x p : ℕ} {e : Expr} {c : Cond} {s t : Stmt}
  {args : List Expr}
end layout
structure Setting (W : ℕ) extends Sizes W where
  /-- The light program. -/
  P : Program
  /-- The code of the whole program. -/
  code : List Instr
  /-- Every procedure body is at its entry, followed by the return sequence, all before the
  dispatcher. -/
  bodyAt : ∀ (p : ℕ) (b : Stmt), P[p]? = some b → ∃ e, entry[p]? = some e ∧
    CodeAt code e (compileStmt toCodeLayout b e ++ epilogue toCodeLayout) ∧
    e + b.size F + epilogueSize ≤ disp
  /-- The dispatcher serves the positions before it. -/
  dispatcherAt : CodeAt code disp (dispatcher disp)
  /-- Every body has width at most F. -/
  width : ∀ b ∈ P, b.width ≤ F
def stepsPerStep (n : ℕ) : ℕ := 2 * n
variable {W : ℕ} (S : Setting W)
structure Start (d : ℕ) (s : Stmt) (σ : State) (pos q : ℕ) (m : ℤ → BitVec W) : Prop
    extends Framed S.toSizes σ q m where
  /-- The code of s is at pos. -/
  codeAt : CodeAt S.code pos (compileStmt S.toCodeLayout s pos)
  /-- It ends at or before the dispatcher. -/
  below : pos + s.size S.F ≤ S.disp
  /-- F local variables and 2 F + 1 temporaries are enough for s. -/
  width : s.width ≤ S.F
  /-- The state holds words. -/
  bounded : σ.Bounded S.lim
  /-- The stack has room for this frame and for F + 1 cells for each further level of calls. -/
  room : q + S.F + (S.F + 1) * (S.lim.depth - d) ≤ S.Q
structure Finished (s : Stmt) (σ' : State) (c pos q : ℕ) (m m' : ℤ → BitVec W) (n : ℕ) : Prop where
  /-- The machine has reached the position after the code. -/
  run : Steps S.code n ⟨pos, m⟩ ⟨pos + s.size S.F, m'⟩
  /-- It took at most stepsPerStep machine steps for each step of the language. -/
  le : n ≤ stepsPerStep S.disp * c
  /-- The memory represents σ' in the same frame. -/
  rel : Rel S.toSizes σ' q m'
  /-- Only cells that a statement in the frame q may write have changed. -/
  agree : AgreeOutside (Writable S.toSizes q) m m'
def Simulates (d : ℕ) (s : Stmt) (σ σ' : State) (c : ℕ) : Prop :=
  ∀ (pos q : ℕ) (m : ℤ → BitVec W), Start S d s σ pos q m →
    ∃ (m' : ℤ → BitVec W) (n : ℕ), Finished S s σ' c pos q m m' n
variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}
section call
variable {p x : ℕ} {args : List Expr}
end call
end Light.Compiler


