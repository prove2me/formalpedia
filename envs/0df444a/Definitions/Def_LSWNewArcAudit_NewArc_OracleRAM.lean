-- Prove2me | Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
-- name    : LSWNewArcAudit_NewArc_OracleRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:41:56.183263+00:00
-- url     : https://prove2.me/theorems/b0c941f3-96cd-468e-b7a2-025431add9c1
-- title:
--   Exact arithmetic oracle programs with charged bitmap access and execution
-- statement:
--   An exact arithmetic oracle machine extends the published real-RAM scalar and pointer instructions with integer address arithmetic, integer memory, a cast from an integer pointer to a real register, individual subset-bitmap reads and writes, value queries, and a halt returning an integer vertex label. Its program is a finite instruction list with no function-valued instructions. Only rational scalar literals are allowed in admissible programs; input coefficients remain arbitrary real numbers.
--
--   One executed instruction costs one unit of additional work, including query dispatch and halting. A query also increments the evaluation counter and returns the integer value of the objective, cast to a real number. Thus a run has two independently specified counts,
--
--   $$Q=\#\{\text{executed query instructions}\},\qquad W=\#\{\text{executed instructions before and including halt}\}.$$
--
--   Numeric registers and pointers start at zero. Input occupies typed scalar memory and all work bitmaps start empty. A bitmap is the denotation of individually addressed bits: no whole-set copy, clear, scan, maximum, reachability, minimizer, or valid-arc instruction exists. The oracle receives a handle to the already represented subset. Invalid bit indices read zero and writes have no effect; invalid code addresses are stuck and charged. After an executed halt the state remains fixed. Division follows the real-RAM total convention, including division by zero returning zero.
--
--   The step function accesses the objective only in the query branch. Iterating it defines a unique deterministic execution; a finite observation is successful only if a halt has actually produced output. These definitions supply reusable operational accounting, without assuming an algorithm, termination, correctness, or a complexity bound.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2 (5 Nov 2015), https://arxiv.org/pdf/1508.04874v2, §13.1, printed/PDF p. 74 (evaluation-oracle convention); §15.2.2, Lemma 79, printed/PDF pp. 84–86 (arithmetic/oracle resource interpretation).

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace LSWNewArcAudit.NewArc

/-!
Exact arithmetic/oracle model for Lee--Sidford--Wong, arXiv:1508.04874v2,
§13.1 p. 74 and Lemma 79 pp. 84--86. The scalar/pointer RAM is the published
SmaleNinth core; the extensions below supply subset bitmaps, evaluation and
vertex output. This is an operational model, not an algorithm or a correctness
assumption. Bitmaps are denoted by finite sets but are accessed one bit at a time.
-/

/-- A fixed finite program. All numeric arguments other than literals are
register numbers or instruction labels. No constructor accepts a function.
`bitWrite` writes one bit of the bank at pointer `bank`, at element pointer
`element`, with value `realReg[value] ≠ 0`. `bitRead` reads one such bit.
`pointerReal` casts one integer pointer to a real scalar.
`query` presents an already represented bitmap to the value oracle.
`halt` returns one integer pointer. -/
inductive OracleInstruction where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | pointerMul (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | bitWrite (bank element value : ℕ)
  | bitRead (dst bank element : ℕ)
  | query (dst bank : ℕ)
  | halt (pointer : ℕ)

abbrev OracleProgram := List OracleInstruction

/-- Only rational scalar literals are permitted. Core accept/reject instructions
are excluded because this extension halts with a vertex, not a Boolean.
This restricts existentially selected programs, never input weights or oracles. -/
def LiteralProgram (program : OracleProgram) : Prop :=
  ∀ op ∈ program, match op with
    | .core (.const _ value) => ∃ r : ℚ, value = (r : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- Static projection of the finite instruction table. Extension instructions
are placeholders in this table and are always dispatched by `oracleStep`.
This table depends only on the program, not on any input or oracle. -/
def coreProgram (program : OracleProgram) : SmaleNinth.RAMProgram :=
  program.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

structure OracleState (n : ℕ) where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  bitmap : ℤ → Finset (Fin n)
  output : Option ℤ
  queries : ℕ
  work : ℕ

/-- The two scalar sorts of an exact arithmetic RAM. The input is stored in
integer and real cells, not in registers, and contains no oracle or program. -/
structure RAMInput where
  integers : ℤ → ℤ
  reals : ℤ → ℝ

/-- The represented input occupies RAM memory. Registers/pointers start at zero,
all work bitmaps are empty, and no output or uncharged oracle answer is supplied. -/
def oracleInitial {n : ℕ} (input : RAMInput) : OracleState n :=
  ⟨⟨0, fun _ => 0, fun _ => 0, input.reals⟩, input.integers,
    fun _ => ∅, none, 0, 0⟩

/-- One instruction costs one unit of additional work, including query dispatch
and the halt instruction. A query also costs one evaluation. Scalar arithmetic,
comparison, indirect load/store, pointer update, one-bit read/write, jumps and
output are the only operations. There are no whole-set copies, scans, clears,
maxima, graph searches, permutation transforms or validity tests.

An evaluation receives a handle to an existing bitmap: `Finset` denotes its
contents, not a free serialization/copy instruction. A fresh bitmap denotes
zero-initialized RAM; every change is a charged one-bit write. Negative or
out-of-ground-set bit indices read zero and writes do nothing. Invalid code
addresses are stuck, charged, and never produce output. After halt, states
stutter without further work. Division has the core's total convention x/0=0.
`f` occurs only in the query branch. -/
noncomputable def oracleStep {n : ℕ} (program : OracleProgram)
    (f : Finset (Fin n) → ℤ) (s : OracleState n) : OracleState n := by
  classical
  exact if s.output.isSome then s else
    let t := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match program[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) =>
        { t with core := SmaleNinth.RAMStep (coreProgram program) s.core }
    | some (.pointerAdd d a b) =>
        { t with core := { t.core with ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub d a b) =>
        { t with core := { t.core with ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.pointerMul d a b) =>
        { t with core := { t.core with ptrs := Function.update s.core.ptrs d (s.core.ptrs a * s.core.ptrs b) } }
    | some (.integerLoad d a) =>
        { t with core := { t.core with ptrs := Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory := Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.bitWrite b e v) =>
        if h : 0 ≤ s.core.ptrs e ∧ (s.core.ptrs e).toNat < n then
          let j : Fin n := ⟨(s.core.ptrs e).toNat, h.2⟩
          let bank := s.core.ptrs b
          let contents := if s.core.regs v = 0 then (s.bitmap bank).erase j
            else insert j (s.bitmap bank)
          { t with bitmap := Function.update s.bitmap bank contents }
        else t
    | some (.bitRead d b e) =>
        let value : ℝ := if h : 0 ≤ s.core.ptrs e ∧ (s.core.ptrs e).toNat < n then
          if (⟨(s.core.ptrs e).toNat, h.2⟩ : Fin n) ∈ s.bitmap (s.core.ptrs b)
            then 1 else 0
          else 0
        { t with core := { t.core with regs := Function.update s.core.regs d value } }
    | some (.query d b) =>
        { t with
          queries := s.queries + 1
          core := { t.core with regs := Function.update s.core.regs d (f (s.bitmap (s.core.ptrs b)) : ℝ) } }
    | some (.halt a) => { t with output := some (s.core.ptrs a) }

/-- A finite observation of the unique deterministic execution. Requiring a
`some` output means a halt instruction really executed, not that fuel ran out. -/
noncomputable def oracleRun {n : ℕ} (program : OracleProgram)
    (f : Finset (Fin n) → ℤ) (input : RAMInput) (steps : ℕ) : OracleState n :=
  (oracleStep program f)^[steps] (oracleInitial input)

end LSWNewArcAudit.NewArc


