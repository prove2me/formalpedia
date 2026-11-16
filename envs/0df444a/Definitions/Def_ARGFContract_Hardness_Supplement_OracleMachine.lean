-- Prove2me | Definitions.Def_ARGFContract_Hardness_Supplement_OracleMachine
-- name    : ARGFContract_Hardness_Supplement_OracleMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:03:16.252207+00:00
-- url     : https://prove2.me/theorems/15419729-7ca7-41d9-89b7-67e7168b37bc
-- title:
--   Value-oracle real RAM with unit-cost instructions and charged oracle queries
-- statement:
--   A **value-oracle program** is a finite list of instructions over real registers, integer pointer registers, a real memory $\mathbb Z\to\mathbb R$ and an integer memory $\mathbb Z\to\mathbb Z$, extending the published real RAM `SmaleNinth_RealRAM`. Its instructions are: real constants (rational only, for admissible programs), real addition, subtraction, multiplication and division, indirect real load and store, pointer set, copy, increment, decrement, addition and subtraction, integer load and store, an integer-to-real cast, conditional jumps on a real register $\le0$ or on a pointer comparison, insertion or deletion of one agent in a **working committee** $W\subseteq E$, a **query** that writes $f(W)$ to a register and records $W$ in the query trace, and **halt**.
--
--   Each executed instruction costs one step. If evaluating $f$ on an $m$-set costs $\tau(m)$, a run that halts after $t$ steps with query trace $W_1,\dots,W_q$ has running time
--
--   $$t+\sum_{r=1}^{q}\tau(|W_r|).$$
--
--   The output is the working committee and real register $0$ at the halt. The input is the costs $c_i$ (real cells $0,\dots,N-1$), the competencies $p_i$ (real cells $N,\dots,2N-1$), and $N$, the number of labels and the label of each agent (integer cells $0$, $1$ and $2,\dots,N+1$).
--
--   This model gives the running-time claims of Theorems 3, 4, 8 and 9 a precise meaning: real data are compared and combined at unit cost, and nothing sorts, maximizes, copies or scans a set for free.
--
--   **Formalization Note** There is no real-to-integer cast, so cost and competency data influence control flow only through real comparisons. Execution outside the program is stuck and never halts. Division by zero follows the core's total convention. "Time up to oracle evaluations" is the case $\tau=0$, where each query still costs one step.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, STOC 2027 submission #348 (October 2026), Definition 2.1(3), p. 6; running-time claims of Theorems 3, 4, 8, 9 (pp. 14–15, 20–22, 38–42)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open Finset

namespace ARGFContract.Hardness.Supplement

/-!
A value-oracle dialect of the published real RAM (`SmaleNinth.RAMInstr`) for the offline
algorithms of §3.1.2–3.1.4 and Appendices B.2–B.3. Every executed instruction costs one
step. Besides the real-RAM core (real arithmetic, real memory, pointer set/copy/inc/dec,
branches) a program has integer pointer addition and subtraction, an integer memory with
pointer load/store, an integer-to-real cast, one-agent insertion into and deletion from a
working committee, and a value query of `f` on the working committee. There is no
instruction that sorts, maximizes, copies or scans a set, and no real-to-integer cast.
-/

/-- An instruction. Numeric arguments are register numbers or jump targets. -/
inductive OracleInstr where
  /-- A real-RAM instruction; `accept`/`reject` are excluded by `Admissible`. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `ptr[dst] := ptr[a] + ptr[b]`. -/
  | padd (dst a b : ℕ)
  /-- `ptr[dst] := ptr[a] − ptr[b]`. -/
  | psub (dst a b : ℕ)
  /-- `ptr[dst] := intMem[ptr[addr]]`. -/
  | iload (dst addr : ℕ)
  /-- `intMem[ptr[addr]] := ptr[src]`. -/
  | istore (addr src : ℕ)
  /-- `reg[dst] := (ptr[src] : ℝ)`. -/
  | ptoReal (dst src : ℕ)
  /-- Insert agent number `ptr[e]` into the working committee (no effect if out of range). -/
  | insertAgent (e : ℕ)
  /-- Delete agent number `ptr[e]` from the working committee (no effect if out of range). -/
  | eraseAgent (e : ℕ)
  /-- `reg[dst] := f(working committee)`; the queried committee is appended to the trace. -/
  | query (dst : ℕ)
  /-- Stop. The output is the working committee and the real register `0`. -/
  | halt

/-- A program: a finite instruction list executed from position `0`. -/
abbrev OracleProgram := List OracleInstr

/-- Only rational real constants, and no core `accept`/`reject`. This restricts programs,
never the real input data. -/
def Admissible (P : OracleProgram) : Prop :=
  ∀ ins ∈ P, match ins with
    | .core (.const _ r) => ∃ q : ℚ, r = (q : ℝ)
    | .core .accept => False
    | .core .reject => False
    | _ => True

/-- A machine state: real-RAM configuration, integer memory, working committee, and the
chronological list of committees queried so far. -/
structure OracleState (n : ℕ) where
  core : SmaleNinth.RAMConfig
  intMem : ℤ → ℤ
  work : Finset (Fin n)
  queries : List (Finset (Fin n))

/-- The agent with number `z`, if `0 ≤ z < n`. -/
def agentAt (n : ℕ) (z : ℤ) : Option (Fin n) :=
  if h : 0 ≤ z ∧ z.toNat < n then some ⟨z.toNat, h.2⟩ else none

/-- One step. A state whose program counter is outside the program, at `halt`, or at a core
`accept`/`reject` does not move (outside the program it is stuck and never halts). The value
oracle `f` is consulted only by `query`. Division is the core's total `x / 0 = 0`. -/
noncomputable def oracleStep {n : ℕ} (P : OracleProgram) (f : Finset (Fin n) → ℝ)
    (s : OracleState n) : OracleState n :=
  let pc := s.core.pc
  let next : SmaleNinth.RAMConfig := { s.core with pc := pc + 1 }
  match P[pc]? with
  | none => s
  | some .halt => s
  | some (.core .accept) => s
  | some (.core .reject) => s
  | some (.core (.jle i target)) =>
      { s with core := { s.core with pc := if s.core.regs i ≤ 0 then target else pc + 1 } }
  | some (.core (.pjle q q' target)) =>
      { s with core := { s.core with
          pc := if s.core.ptrs q ≤ s.core.ptrs q' then target else pc + 1 } }
  | some (.core i) =>
      { s with core := { SmaleNinth.RAMStep [i] { s.core with pc := 0 } with pc := pc + 1 } }
  | some (.padd d a b) =>
      { s with core := { next with
          ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
  | some (.psub d a b) =>
      { s with core := { next with
          ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
  | some (.iload d a) =>
      { s with core := { next with
          ptrs := Function.update s.core.ptrs d (s.intMem (s.core.ptrs a)) } }
  | some (.istore a b) =>
      { s with core := next,
               intMem := Function.update s.intMem (s.core.ptrs a) (s.core.ptrs b) }
  | some (.ptoReal d a) =>
      { s with core := { next with
          regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
  | some (.insertAgent e) =>
      match agentAt n (s.core.ptrs e) with
      | some j => { s with core := next, work := insert j s.work }
      | none => { s with core := next }
  | some (.eraseAgent e) =>
      match agentAt n (s.core.ptrs e) with
      | some j => { s with core := next, work := s.work.erase j }
      | none => { s with core := next }
  | some (.query d) =>
      { s with core := { next with regs := Function.update s.core.regs d (f s.work) },
               queries := s.queries ++ [s.work] }

/-- The initial state on real input memory `reals` and integer input memory `ints`:
program counter, registers and pointers zero, empty working committee, empty trace. -/
def initState (n : ℕ) (reals : ℤ → ℝ) (ints : ℤ → ℤ) : OracleState n :=
  ⟨⟨0, fun _ => 0, fun _ => 0, reals⟩, ints, ∅, []⟩

/-- Real input layout: cell `i` holds the cost `c_i` and cell `n + i` the competency `p_i`
(`0 ≤ i < n`); all other cells hold `0`. -/
noncomputable def encodeReals {n : ℕ} (c p : Fin n → ℝ) : ℤ → ℝ := fun z =>
  if h : 0 ≤ z ∧ z.toNat < n then c ⟨z.toNat, h.2⟩
  else if h' : (n : ℤ) ≤ z ∧ (z - n).toNat < n then p ⟨(z - n).toNat, h'.2⟩
  else 0

/-- Integer input layout: cell `0` holds `n`, cell `1` the number `m` of labels, cell `2 + i`
the label of agent `i` (its bucket, class or cluster); all other cells hold `0`. -/
def encodeInts {n : ℕ} (m : ℕ) (lab : Fin n → ℕ) : ℤ → ℤ := fun z =>
  if z = 0 then (n : ℤ) else if z = 1 then (m : ℤ)
  else if h : 2 ≤ z ∧ (z - 2).toNat < n then (lab ⟨(z - 2).toNat, h.2⟩ : ℤ)
  else 0

/-- The state after `t` steps. -/
noncomputable def oracleRun {n : ℕ} (P : OracleProgram) (f : Finset (Fin n) → ℝ)
    (s₀ : OracleState n) (t : ℕ) : OracleState n :=
  (oracleStep P f)^[t] s₀

/-- The state is at a `halt` instruction. -/
def IsHalted {n : ℕ} (P : OracleProgram) (s : OracleState n) : Prop :=
  P[s.core.pc]? = some OracleInstr.halt

/-- Total oracle evaluation time of the trace when evaluating `f` on a committee of size `m`
costs `τ m` time units (Definition 2.1(3)). -/
def oracleTime {n : ℕ} (τ : ℕ → ℕ) (s : OracleState n) : ℕ :=
  (s.queries.map (fun S => τ S.card)).sum

/-- `P` halts within `T` time units — `t` executed instructions plus the oracle evaluation
time `τ` of its queries — and its output committee `S`, real output `reg 0` and query trace
`Q` satisfy `Out S (reg 0) Q`. With `τ = 0` this measures time up to the cost of oracle
evaluations (each query still costs one step). -/
def RunsWithin {n : ℕ} (P : OracleProgram) (f : Finset (Fin n) → ℝ) (τ : ℕ → ℕ)
    (s₀ : OracleState n) (T : ℕ)
    (Out : Finset (Fin n) → ℝ → List (Finset (Fin n)) → Prop) : Prop :=
  ∃ t : ℕ, IsHalted P (oracleRun P f s₀ t) ∧
    t + oracleTime τ (oracleRun P f s₀ t) ≤ T ∧
    Out (oracleRun P f s₀ t).work ((oracleRun P f s₀ t).core.regs 0)
      (oracleRun P f s₀ t).queries

end ARGFContract.Hardness.Supplement


