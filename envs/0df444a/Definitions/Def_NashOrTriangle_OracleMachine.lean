-- Prove2me | Definitions.Def_NashOrTriangle_OracleMachine
-- name    : NashOrTriangle_OracleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:57.584805+00:00
-- url     : https://prove2.me/theorems/8a302d8a-1ea7-4444-aadc-12d75a9fbde6
-- title:
--   The oracle model: programs, labels, transcripts and runs
-- statement:
--   The **oracle model** of the paper. An algorithm is a finite program of a real pointer machine (unit-cost arithmetic and comparisons on numbers in registers and in a random-access memory) extended by four instructions:
--
--   1. a **utility query**, returning the rational number $M(a, b)$ for a known row $a$ and a known column $b$;
--   2. a **maximizing BR query** on a finite rational mixture of known columns, or on $\perp$, returning a row;
--   3. a **minimizing BR query** on a finite rational mixture of known rows, or on $\perp$, returning a column;
--   4. **halt**, after which the answer is read from memory.
--
--   Initially no strategy is known. The algorithm never sees strategies themselves: when a BR call returns a strategy for the first time it receives the smallest unused label ($0, 1, 2, \dots$ in order of first appearance) for that player, and queries and answers are written in labels. The run records a label-level **transcript** (the utility values and the BR queries with the labels returned), the number of utility calls and BR calls, and the number of executed instructions (the steps of local computation). It also records the largest bit length of any number written to a real register (every operand of an arithmetic operation or comparison is such a number) and the largest bit length of a payoff returned by a utility call, so that the paper's bit-length bound on the local computation can be stated.
--
--   **Formalization Note** The arithmetic core is the published `SmaleNinth.RAMInstr` machine. A query mixture is written in memory as a count $n$ followed by $n$ pairs (label, weight), with $n = 0$ meaning $\perp$. A query naming an unknown label, or whose weights are not nonnegative rationals summing to $1$, leaves the machine stuck (charged, never halting). Every executed instruction, oracle calls and halt included, costs one unit of `work`. `LiteralProgram` restricts programs to rational literals (the paper's steps are operations on rationals). The $n$-th BR call is answered by the oracle's answer for index $n$. The bit length of a rational $n/d$ in lowest terms is the binary length of $|n|$ plus that of $d$; numbers that are not rational get $0$, a junk value that never occurs in a run of a literal program on rational input.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.4 (PDF p.5); after Theorem 2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_NashOrTriangle_BRAdversary

namespace NashOrTriangle

/-!
The oracle model of Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite
Zero-Sum Games*, STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 4
(PDF p. 5), and the notion of a step of local computation after Theorem 2.1, printed p. 5
(PDF p. 6): "Each step is an arithmetic operation or a comparison on rationals".

A deterministic algorithm is a finite program of the published real pointer machine
`SmaleNinth.RAMInstr` (unit-cost arithmetic and comparisons, indirect memory `ℤ → ℝ`), extended
by a utility query, a maximizing and a minimizing best-response query, and a halt instruction.
The algorithm sees strategies only through their labels: "When a BR call returns a strategy for
the first time, it receives the smallest unused integer label for that player" (labels are
`0, 1, 2, …` in order of first appearance), and "initially no strategy is known but [we] allow
making a maximizing or a minimizing query to the BR oracle with p = ⊥ or q = ⊥".
-/

/-- An instruction. `core` is a real-RAM instruction. `pointerReal dst q`: `r[dst] := p[q]`.
`utility dst i j`: `r[dst] := M(row with label p[i], column with label p[j])`.
`maxBR dst base`: a maximizing BR query on the column mixture written in memory at address
`p[base]` (a count `n`, then `n` pairs label, weight; `n = 0` is `⊥`); the label of the returned
row is put in `p[dst]`. `minBR dst base`: the same for a row mixture, returning a column label.
`halt base`: stop; the answer is the memory region starting at address `p[base]`. -/
inductive Instr where
  | core (i : SmaleNinth.RAMInstr)
  | pointerReal (dst q : ℕ)
  | utility (dst i j : ℕ)
  | maxBR (dst base : ℕ)
  | minBR (dst base : ℕ)
  | halt (base : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Only rational literals, and no Boolean accept/reject (the algorithm halts with an answer).
The paper's local steps are operations on rationals; real literals would carry unbounded
advice. This restricts the programs, never the games or the oracles. -/
def LiteralProgram (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ c) => ∃ r : ℚ, c = (r : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static real-RAM table of a program; extension instructions are placeholders here and are
dispatched by `step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- An entry of the label-level transcript: what the algorithm sees. `utility i j v`: the utility
query on row label `i` and column label `j` returned `v`. `maxBR q l`: the maximizing query on the
column-label mixture `q` (`none` = `⊥`) returned the row with label `l`; `minBR` likewise. -/
inductive Event where
  | utility (i j : ℕ) (v : ℚ)
  | maxBR (q : Option (ℕ →₀ ℚ)) (label : ℕ)
  | minBR (p : Option (ℕ →₀ ℚ)) (label : ℕ)

/-- A machine state: the real-RAM configuration, the known rows and columns (the label of a
strategy is its index in the list), the transcript, the counters of utility calls, BR calls and
executed instructions, the largest bit length of a number written to a real register so far
(`bits`), the largest bit length of a payoff returned by a utility call so far (`payBits`), and
the output address once halted. -/
structure State (A B : Type*) where
  core : SmaleNinth.RAMConfig
  rows : List A
  cols : List B
  transcript : List Event
  utilCalls : ℕ
  brCalls : ℕ
  work : ℕ
  bits : ℕ
  payBits : ℕ
  output : Option ℤ

/-- The bit length of a rational number `x = n/d` in lowest terms: the binary length of `|n|`
plus that of `d`. Real numbers that are not rational get `0`; they never occur in a run of a
`LiteralProgram` on rational input memory (literals, inputs and payoffs are rational, and the
arithmetic instructions preserve rationality, `x / 0 = 0` included), so the junk value is never
used by the theorems that bound `bits`. -/
noncomputable def ratBits (x : ℝ) : ℕ := by
  classical
  exact if h : ∃ r : ℚ, (r : ℝ) = x then h.choose.num.natAbs.size + h.choose.den.size else 0

/-- The bit length of the number a core instruction writes to a real register (`0` for the
instructions that write none), read off the configuration after the instruction. -/
noncomputable def coreBits (i : SmaleNinth.RAMInstr) (c : SmaleNinth.RAMConfig) : ℕ :=
  match i with
  | .const d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .div d _ _ | .load d _ => ratBits (c.regs d)
  | _ => 0

/-- Read a natural number from a memory cell (`none` unless the cell holds one). -/
noncomputable def readNat (x : ℝ) : Option ℕ := by
  classical
  exact if h : ∃ n : ℕ, (n : ℝ) = x then some (Nat.find h) else none

/-- Read a rational number from a memory cell (`none` unless the cell holds one). -/
noncomputable def readRat (x : ℝ) : Option ℚ := by
  classical
  exact if h : ∃ r : ℚ, (r : ℝ) = x then some h.choose else none

/-- Read `n` pairs (label, weight) from cells `base, base + 1, …`; repeated labels add up. -/
noncomputable def readPairs (mem : ℤ → ℝ) (base : ℤ) : ℕ → Option (ℕ →₀ ℚ)
  | 0 => some 0
  | n + 1 => (readPairs mem base n).bind fun f =>
      (readNat (mem (base + 2 * (n : ℤ)))).bind fun l =>
        (readRat (mem (base + 2 * (n : ℤ) + 1))).map fun w => f + Finsupp.single l w

/-- Read a label mixture at `base`: the count `n` in cell `base`, then `n` pairs (label, weight).
Returns the count and the mixture. -/
noncomputable def readMix (mem : ℤ → ℝ) (base : ℤ) : Option (ℕ × (ℕ →₀ ℚ)) :=
  (readNat (mem base)).bind fun n => (readPairs mem (base + 1) n).map fun f => (n, f)

/-- A label mixture is well formed for `n` known strategies: a finite rational mixture all of
whose labels are below `n`. -/
def ValidLabelMix (n : ℕ) (q : ℕ →₀ ℚ) : Prop :=
  IsFinMix q ∧ ∀ l ∈ q.support, l < n

/-- The mixture of strategies named by a label mixture, through the list of known strategies. -/
noncomputable def labelMix {α : Type*} (L : List α) (q : ℕ →₀ ℚ) : α →₀ ℚ :=
  q.sum fun l w => match L[l]? with
    | some x => Finsupp.single x w
    | none => 0

/-- The initial state on input memory `x`: program counter and registers `0`, nothing known. -/
def initState (A B : Type*) (x : ℤ → ℝ) : State A B :=
  ⟨⟨0, fun _ => 0, fun _ => 0, x⟩, [], [], [], 0, 0, 0, 0, 0, none⟩

/-- One step. Every executed instruction costs one unit of `work`, including oracle calls and
`halt`; utility and BR instructions also count as calls. A halted state stutters with no further
work. An invalid program address, a utility query on an unknown label, or a BR query whose
memory is not a well-formed mixture of known strategies (labels below the current count,
nonnegative rational weights summing to `1`) is stuck: charged, never producing output. A BR
answer that is a new strategy gets the smallest unused label (it is appended); a known strategy
keeps its label. The `n`-th BR call (from `0`) is answered by `adv.row n` or `adv.col n`.
`bits` records the bit length of every number written to a real register (by an arithmetic or
load instruction, `pointerReal` or a utility call); every operand of an arithmetic operation or
comparison is such a number or the initial `0`, so `bits` bounds the bit length of all numbers
the local computation operates on. `payBits` records the bit length of every payoff returned by
a utility call. -/
noncomputable def step {A B : Type*} (P : Program) (M : A → B → ℚ) {δ : ℝ}
    (adv : BRAdversary M δ) (s : State A B) : State A B := by
  classical
  exact
    if s.output.isSome then s else
    let nxt : State A B := { s with work := s.work + 1, core := { s.core with pc := s.core.pc + 1 } }
    let stuck : State A B := { s with work := s.work + 1, core := { s.core with pc := P.length } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core i) =>
        let c' := SmaleNinth.RAMStep (coreProgram P) s.core
        { nxt with core := c', bits := max s.bits (coreBits i c') }
    | some (.pointerReal d q) =>
        { nxt with
          bits := max s.bits (ratBits (s.core.ptrs q : ℝ))
          core := { nxt.core with regs := Function.update s.core.regs d (s.core.ptrs q : ℝ) } }
    | some (.utility d i j) =>
        if 0 ≤ s.core.ptrs i ∧ 0 ≤ s.core.ptrs j then
          match s.rows[(s.core.ptrs i).toNat]?, s.cols[(s.core.ptrs j).toNat]? with
          | some a, some b =>
              { nxt with
                utilCalls := s.utilCalls + 1
                bits := max s.bits (ratBits (M a b : ℝ))
                payBits := max s.payBits (ratBits (M a b : ℝ))
                transcript := s.transcript ++
                  [Event.utility (s.core.ptrs i).toNat (s.core.ptrs j).toNat (M a b)]
                core := { nxt.core with regs := Function.update s.core.regs d (M a b : ℝ) } }
          | _, _ => stuck
        else stuck
    | some (.maxBR d bse) =>
        match readMix s.core.mem (s.core.ptrs bse) with
        | none => stuck
        | some (n, q) =>
            if n = 0 ∨ ValidLabelMix s.cols.length q then
              let query : Option (ℕ →₀ ℚ) := if n = 0 then none else some q
              let x := adv.row s.brCalls (query.map (labelMix s.cols))
              let lab := if x ∈ s.rows then s.rows.idxOf x else s.rows.length
              { nxt with
                rows := if x ∈ s.rows then s.rows else s.rows ++ [x]
                brCalls := s.brCalls + 1
                transcript := s.transcript ++ [Event.maxBR query lab]
                core := { nxt.core with ptrs := Function.update s.core.ptrs d (lab : ℤ) } }
            else stuck
    | some (.minBR d bse) =>
        match readMix s.core.mem (s.core.ptrs bse) with
        | none => stuck
        | some (n, p) =>
            if n = 0 ∨ ValidLabelMix s.rows.length p then
              let query : Option (ℕ →₀ ℚ) := if n = 0 then none else some p
              let y := adv.col s.brCalls (query.map (labelMix s.rows))
              let lab := if y ∈ s.cols then s.cols.idxOf y else s.cols.length
              { nxt with
                cols := if y ∈ s.cols then s.cols else s.cols ++ [y]
                brCalls := s.brCalls + 1
                transcript := s.transcript ++ [Event.minBR query lab]
                core := { nxt.core with ptrs := Function.update s.core.ptrs d (lab : ℤ) } }
            else stuck
    | some (.halt bse) => { nxt with output := some (s.core.ptrs bse) }

/-- The state after `n` steps of `P` on game `M` with oracle `adv` and input memory `x`. -/
noncomputable def run {A B : Type*} (P : Program) (M : A → B → ℚ) {δ : ℝ}
    (adv : BRAdversary M δ) (x : ℤ → ℝ) (n : ℕ) : State A B :=
  (step P M adv)^[n] (initState A B x)

end NashOrTriangle


