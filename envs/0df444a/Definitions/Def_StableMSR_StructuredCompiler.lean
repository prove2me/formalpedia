-- Prove2me | Definitions.Def_StableMSR_StructuredCompiler
-- name    : StableMSR_StructuredCompiler
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T19:33:26.754804+00:00
-- url     : https://prove2.me/theorems/1bb1b070-9b81-4389-91ea-b21492695877
-- title:
--   Structured deterministic programs and exact charged execution
-- statement:
--   A structured deterministic language over the recovery interpreter: rational real primitives, integer pointers and memory, tests, sequencing, and while loops. Its finite execution relation records exact instruction charges, including branch and loop control. Compilation relocates absolute jump targets into a finite instruction list and appends a charged halt. Store conversion preserves all machine data; the execution relation supplies finite termination evidence rather than assuming termination of arbitrary loops.
-- source:
--   Structured-program compiler developed for the Exact Sum-of-Radii Clustering under Any Constant Stability mission; instruction model Definitions.Def_StableMSR_Recovery_Execution and the accepted array_minimum_program proof https://prove2.me/theorems/0aea05ce-c128-4474-ad63-c10e32c5a519.

import Definitions.Def_StableMSR_Recovery_Execution
import Mathlib.Tactic
set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery
namespace StableMSR.Recovery.Compiler
structure Store where
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ
  imem : ℤ → ℤ
  tapePos : ℕ
  queries : ℕ
  output : ℝ


def Store.state (s : Store) (pc work : ℕ) : MinSumFPT.State :=
  ⟨⟨pc, s.regs, s.ptrs, s.mem⟩, s.imem, s.tapePos, work, s.queries, false, s.output⟩

/- Deterministic straight-line primitives; real literals are syntactically rational. -/

inductive Op where
  | realConst (dst : ℕ) (value : ℚ)
  | realAdd (dst a b : ℕ)
  | realSub (dst a b : ℕ)
  | realMul (dst a b : ℕ)
  | realDiv (dst a b : ℕ)
  | realLoad (dst address : ℕ)
  | realStore (address src : ℕ)
  | pointerConst (dst : ℕ) (value : ℤ)
  | pointerCopy (dst src : ℕ)
  | pointerInc (dst : ℕ)
  | pointerDec (dst : ℕ)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst src : ℕ)
  | distance (dst a b : ℕ)


noncomputable def Op.instr : Op → MinSumFPT.Instr
  | .realConst dst q => .core (.const dst (q : ℝ))
  | .realAdd dst a b => .core (.add dst a b)
  | .realSub dst a b => .core (.sub dst a b)
  | .realMul dst a b => .core (.mul dst a b)
  | .realDiv dst a b => .core (.div dst a b)
  | .realLoad dst a => .core (.load dst a)
  | .realStore a src => .core (.store a src)
  | .pointerConst dst z => .core (.pset dst z)
  | .pointerCopy dst src => .core (.pcopy dst src)
  | .pointerInc dst => .core (.pinc dst)
  | .pointerDec dst => .core (.pdec dst)
  | .pointerAdd dst a b => .pointerAdd dst a b
  | .pointerSub dst a b => .pointerSub dst a b
  | .integerLoad dst a => .integerLoad dst a
  | .integerStore a src => .integerStore a src
  | .pointerReal dst src => .pointerReal dst src
  | .distance dst a b => .dist dst a b


noncomputable def Op.eval {n : ℕ} (d : Point n → Point n → ℝ) (op : Op) (s : Store) : Store :=
  match op with
  | .realConst dst q => { s with regs := Function.update s.regs dst (q : ℝ) }
  | .realAdd dst a b => { s with regs := Function.update s.regs dst (s.regs a + s.regs b) }
  | .realSub dst a b => { s with regs := Function.update s.regs dst (s.regs a - s.regs b) }
  | .realMul dst a b => { s with regs := Function.update s.regs dst (s.regs a * s.regs b) }
  | .realDiv dst a b => { s with regs := Function.update s.regs dst (s.regs a / s.regs b) }
  | .realLoad dst a => { s with regs := Function.update s.regs dst (s.mem (s.ptrs a)) }
  | .realStore a src => { s with mem := Function.update s.mem (s.ptrs a) (s.regs src) }
  | .pointerConst dst z => { s with ptrs := Function.update s.ptrs dst z }
  | .pointerCopy dst src => { s with ptrs := Function.update s.ptrs dst (s.ptrs src) }
  | .pointerInc dst => { s with ptrs := Function.update s.ptrs dst (s.ptrs dst + 1) }
  | .pointerDec dst => { s with ptrs := Function.update s.ptrs dst (s.ptrs dst - 1) }
  | .pointerAdd dst a b => { s with ptrs := Function.update s.ptrs dst (s.ptrs a + s.ptrs b) }
  | .pointerSub dst a b => { s with ptrs := Function.update s.ptrs dst (s.ptrs a - s.ptrs b) }
  | .integerLoad dst a => { s with ptrs := Function.update s.ptrs dst (s.imem (s.ptrs a)) }
  | .integerStore a src => { s with imem := Function.update s.imem (s.ptrs a) (s.ptrs src) }
  | .pointerReal dst src => { s with regs := Function.update s.regs dst (s.ptrs src : ℝ) }
  | .distance dst a b =>
      { s with regs := Function.update s.regs dst (MinSumFPT.oracleAnswer d (s.ptrs a) (s.ptrs b)), queries := s.queries + 1 }


inductive Cond where
  | realNonpos (reg : ℕ)
  | pointerLE (a b : ℕ)


def Cond.test (c : Cond) (s : Store) : Prop :=
  match c with
  | .realNonpos r => s.regs r ≤ 0
  | .pointerLE a b => s.ptrs a ≤ s.ptrs b


noncomputable instance (c : Cond) (s : Store) : Decidable (c.test s) := Classical.propDecidable _


def Cond.instr (c : Cond) (target : ℕ) : MinSumFPT.Instr :=
  match c with
  | .realNonpos r => .core (.jle r target)
  | .pointerLE a b => .core (.pjle a b target)


def jump (target : ℕ) : MinSumFPT.Instr := .core (.pjle 0 0 target)


def Contains (P : MinSumFPT.Program) (pc : ℕ) (code : MinSumFPT.Program) : Prop :=
  ∀ i, i < code.length → P[pc+i]? = code[i]?


inductive Cmd where
  | skip
  | atom (op : Op)
  | seq (first second : Cmd)
  | ite (c : Cond) (yes no : Cmd)
  | whileDo (c : Cond) (body : Cmd)


def Cmd.size : Cmd → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq a b => a.size + b.size
  | .ite _ yes no => 1 + no.size + 1 + yes.size
  | .whileDo _ body => 2 + body.size + 1

/- Absolute branch destinations are computed from the block's actual location. -/

noncomputable def compileAt (pc : ℕ) : Cmd → MinSumFPT.Program
  | .skip => []
  | .atom op => [op.instr]
  | .seq a b => compileAt pc a ++ compileAt (pc+a.size) b
  | .ite c yes no => c.instr (pc+1+no.size+1) ::
      (compileAt (pc+1) no ++ jump (pc+1+no.size+1+yes.size) ::
        compileAt (pc+1+no.size+1) yes)
  | .whileDo c body => c.instr (pc+2) :: jump (pc+2+body.size+1) ::
      (compileAt (pc+2) body ++ [jump pc])


inductive Executes {n : ℕ} (d : Point n → Point n → ℝ) : Cmd → Store → Store → ℕ → Prop
  | skip (s : Store) : Executes d .skip s s 0
  | atom (op : Op) (s : Store) : Executes d (.atom op) s (op.eval d s) 1
  | seq {a b : Cmd} {s t u : Store} {i j : ℕ} :
      Executes d a s t i → Executes d b t u j → Executes d (.seq a b) s u (i+j)
  | ite_true {c : Cond} {yes no : Cmd} {s t : Store} {i : ℕ} :
      c.test s → Executes d yes s t i → Executes d (.ite c yes no) s t (1+i)
  | ite_false {c : Cond} {yes no : Cmd} {s t : Store} {i : ℕ} :
      ¬ c.test s → Executes d no s t i → Executes d (.ite c yes no) s t (1+i+1)
  | while_false {c : Cond} {body : Cmd} {s : Store} :
      ¬ c.test s → Executes d (.whileDo c body) s s 2
  | while_true {c : Cond} {body : Cmd} {s t u : Store} {i j : ℕ} :
      c.test s → Executes d body s t i → Executes d (.whileDo c body) t u j →
      Executes d (.whileDo c body) s u (1+i+1+j)


def SafeInstr (i : MinSumFPT.Instr) : Prop :=
  ((∀ dst c, i = .core (.const dst c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject) ∧
    match i with | .unif _ | .uniformIndex _ _ => False | _ => True


def BoundedExec {n : ℕ} (d : Point n → Point n → ℝ) (cmd : Cmd)
    (s t : Store) (budget : ℕ) : Prop := ∃ cost ≤ budget, Executes d cmd s t cost

/- A finite loop invariant chain yields the explicit body-plus-control budget.
Each body costs at most B; each iteration costs two additional instructions,
and the failed guard plus exit jump costs two. -/

noncomputable def compile (cmd : Cmd) (result : ℕ := 0) : MinSumFPT.Program :=
  compileAt 0 cmd ++ [.halt result]


def Store.haltedState (s : Store) (pc w result : ℕ) : MinSumFPT.State :=
  { s.state pc w with halted := true, output := s.regs result }


def initialStore (n k : ℕ) : Store :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0,
    fun a => if a = 0 then (n : ℤ) else if a = 1 then (k : ℤ) else 0, 0, 0, 0⟩

end StableMSR.Recovery.Compiler


