-- Prove2me | Definitions.Def_TwoAgentLateDP2004_LateLate_RAM
-- name    : TwoAgentLateDP2004_LateLate_RAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:47:05.982892+00:00
-- url     : https://prove2.me/theorems/299c1c6a-2b47-4027-9291-5effed129066
-- title:
--   Finite real-oracle RAM programs and charged execution semantics
-- statement:
--   A finite program combines returns, primitive instructions and continuations. Instructions read and write random-access memory, read a job owner or numeric datum, add and compare extended real values, take a minimum, test finiteness, perform bounded-index arithmetic, convert an integer budget, or charge branch and loop control. One interpreted execution returns a value, final memory and a step count:
--   $$T(\operatorname{return})=T(\operatorname{instruction})=1,\qquad T(\operatorname{bind}(p,f))=T(p)+T(f(\operatorname{value}(p)))+1.$$
--   Memory uses extensional random-access semantics; each write changes exactly its addressed cell. Loop tests, increments and branches are emitted into the program. Real comparisons use oracle semantics, so this measures the paper's unit-cost arithmetic model, without a bit-complexity claim. Increasing bounded loops and an owner-counting fold are provided as finite programs. Row-major addressing uses four charged arithmetic instructions. This operational layer is reusable independently of the scheduling correctness statements.
--   **Formalization Note** No instruction evaluates the recurrence, computes an optimum or accepts a correctness/time certificate. Total input reads outside the job range have irrelevant defaults; the fixed tabulator uses only valid input addresses.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici (2004), Scheduling Problems with Two Competing Agents, Operations Research 52(2):229–242, https://doi.org/10.1287/opre.1030.0092, §7, Theorem 7.3 complexity paragraph, p.236 (PDF p.8): constant time per entry; explicit operational encoding

import Mathlib
import Definitions.Def_TwoAgentLateDP2004_LateLate_Model

namespace TwoAgentLateDP2004.LateLate

/-- Unit-cost real arithmetic/random-access instructions. `control` charges a
branch or loop test; bind and return are charged by the interpreter as well.
No instruction invokes the recurrence or solves an optimization problem. -/
inductive Op : Type → Type where
  | read (a : ℕ) : Op (WithTop ℝ)
  | write (a : ℕ) (v : WithTop ℝ) : Op Unit
  | processing (j : ℕ) : Op (WithTop ℝ)
  | due (j : ℕ) : Op (WithTop ℝ)
  | owner (j : ℕ) : Op Bool
  | add (x y : WithTop ℝ) : Op (WithTop ℝ)
  | le (x y : WithTop ℝ) : Op Bool
  | minimum (x y : WithTop ℝ) : Op (WithTop ℝ)
  | finite (x : WithTop ℝ) : Op Bool
  | nadd (x y : ℕ) : Op ℕ
  | nsub (x y : ℕ) : Op ℕ
  | nmul (x y : ℕ) : Op ℕ
  | nmin (x y : ℕ) : Op ℕ
  | zero (x : ℕ) : Op Bool
  | negative (x : ℤ) : Op Bool
  | toNat (x : ℤ) : Op ℕ
  | control : Op Unit

/-- A finite oracle program. Continuations depend on returned register values;
real comparisons are interpreted classically, without rationalizing the inputs. -/
inductive Code : Type → Type 1 where
  | ret {α : Type} (x : α) : Code α
  | instr {α : Type} (o : Op α) : Code α
  | bind {α β : Type} (p : Code α) (f : α → Code β) : Code β

instance : Monad Code where
  pure := Code.ret
  bind := Code.bind

abbrev Memory := ℕ → WithTop ℝ

/-- Total semantics of a single instruction; input addresses outside n are
irrelevant defaults. Random-access updates have the usual extensional semantics,
not a linear list lookup. The cost model charges each such instruction one. -/
noncomputable def opEval {n : ℕ} (I : Input n) {α : Type} : Op α → Memory → α × Memory
  | .read a, m => (m a, m)
  | .write a v, m => ((), Function.update m a v)
  | .processing j, m => (if h : j < n then (I.p ⟨j, h⟩ : WithTop ℝ) else 0, m)
  | .due j, m => (if h : j < n then (I.d ⟨j, h⟩ : WithTop ℝ) else 0, m)
  | .owner j, m => (if h : j < n then I.owner ⟨j, h⟩ else false, m)
  | .add x y, m => (x + y, m)
  | .le x y, m => (decide (x ≤ y), m)
  | .minimum x y, m => (min x y, m)
  | .finite x, m => (decide (x ≠ ⊤), m)
  | .nadd x y, m => (x + y, m)
  | .nsub x y, m => (x - y, m)
  | .nmul x y, m => (x * y, m)
  | .nmin x y, m => (min x y, m)
  | .zero x, m => (decide (x = 0), m)
  | .negative x, m => (decide (x < 0), m)
  | .toNat x, m => (x.toNat, m)
  | .control, m => ((), m)

/-- Returned value, final RAM, actual charged execution steps. Every constructor
costs one; a bind additionally includes both executed subprogram costs. -/
noncomputable def execute {n : ℕ} (I : Input n) {α : Type} : Code α → Memory → α × Memory × ℕ
  | .ret x, m => (x, m, 1)
  | .instr o, m => let z := opEval I o m; (z.1, z.2, 1)
  | .bind p f, m =>
    let z := execute I p m
    let t := execute I (f z.1) z.2.1
    (t.1, t.2.1, z.2.2 + t.2.2 + 1)

/-- Increasing bounded loop [start,start+len). Loop tests and increments are
charged; no preconstructed list of states or recurrence tree is evaluated. -/
def loop (start : ℕ) : ℕ → (ℕ → Code Unit) → Code Unit
  | 0, _ => .instr .control
  | len + 1, body => do
    let _ ← Code.instr Op.control
    body start
    let next ← Code.instr (Op.nadd start 1)
    loop next len body

/-- A bounded fold, used to count A jobs before allocating the DP table. -/
def countA (start : ℕ) : ℕ → ℕ → Code ℕ
  | 0, a => do
    let _ ← Code.instr Op.control
    pure a
  | len + 1, a => do
    let _ ← Code.instr Op.control
    let own ← Code.instr (Op.owner start)
    let _ ← Code.instr Op.control
    let a' ← if own then Code.instr (Op.nadd a 1) else pure a
    let next ← Code.instr (Op.nadd start 1)
    countA next len a'

/-- Row-major address ((i*H)+h)*K+k, as charged RAM arithmetic. -/
def addressCode (H K i h k : ℕ) : Code ℕ := do
  let x ← Code.instr (Op.nmul i H)
  let y ← Code.instr (Op.nadd x h)
  let z ← Code.instr (Op.nmul y K)
  Code.instr (Op.nadd z k)

def address (H K i h k : ℕ) : ℕ := (i * H + h) * K + k

end TwoAgentLateDP2004.LateLate


