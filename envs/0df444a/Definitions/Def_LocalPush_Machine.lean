-- Prove2me | Definitions.Def_LocalPush_Machine
-- name    : LocalPush_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:03:45.806259+00:00
-- url     : https://prove2.me/theorems/7cd0eb3f-400f-4d90-a32e-dd7cbdc9b9e1
-- title:
--   Randomized real RAM with an adjacency-list oracle, a query counter and fair coins
-- statement:
--   The machine on which "there exists an algorithm" is read. A program is a finite list of instructions over:
--
--   1. the published real pointer machine `SmaleNinth.RAMInstr` (real registers, integer pointers, real memory $\mathbb Z\to\mathbb R$; $+,-,\times,\div$, rational literals, indirect load and store, pointer set, copy, increment, decrement, two comparison jumps);
--   2. integer pointer addition and subtraction, an integer memory, and a pointer-to-real cast;
--   3. `coin`, which reads the next bit of a tape of independent fair coins;
--   4. the two instructions of the adjacency-list model: `deg` returns the degree of a node, and `nbr` returns the neighbor at a given position of a node's list (an invalid node or position returns $-1$);
--   5. `halt`.
--
--   Every executed instruction costs one unit of work; each oracle instruction also counts one query. An invalid program counter is stuck and charged, and a halted state stutters at no cost. `Admissible` requires every literal to be rational and excludes the core's accept and reject.
--
--   The model gives the time and query complexity of Theorem 1.2 a precise meaning.
--
--   **Formalization Note** There is no floor, real-to-integer cast, square root, exponential or logarithm, no pointer multiplication, and no instruction carrying a function, so nothing is computed free of charge.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, adjacency-list model, p.4 (PDF p.4); Theorem 1.2, p.5

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace LocalPush

/-!
# The randomized real RAM with adjacency-list oracle and query counter

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, p.4 (PDF p.4): "Our local
algorithms access the graph through the standard adjacency-list model: querying a node's degree or retrieving
an individual neighbor takes O(1) time." Theorem 1.2 (p.5) speaks of "an algorithm" with a query complexity and
a time complexity, and names no machine, so this model is a reading.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`. The extensions are integer
pointer addition and subtraction, an integer memory, a pointer-to-real cast, a fair-coin instruction, the two
oracle instructions of the adjacency-list model, and `halt`.

**Formalization Note.**
* Instructions: the core's `+ − × ÷` (with `x / 0 = 0`), literals, indirect real load and store, pointer set,
  copy, increment and decrement, the two comparison jumps; `pointerAdd`, `pointerSub`, `integerLoad`,
  `integerStore`, `pointerReal`; `coin`; `deg`, `nbr`; `halt`.
* There is no floor, no real-to-integer cast, no sqrt, rpow, exp or log, no pointer multiplication, and no
  constructor carries a function. Real literals are rational (`Admissible`); this restricts the existentially
  chosen program, never the input.
* The graph is a list of adjacency lists `nbrs : Fin n → List (Fin n)`; node `v` is the pointer value `v`.
  `deg d a` sets `p[d]` to the length of the list of node `p[a]`; `nbr d a b` sets `p[d]` to the entry at
  (0-based) position `p[b]` of the list of node `p[a]`. An invalid node or position returns `−1`. Each oracle
  instruction costs one unit of `work` and one `query`, valid or not. These are the only instructions that read
  the graph.
* Every executed instruction costs one unit of `work`, including jumps, `coin`, the oracle instructions and
  `halt`. An invalid program counter is stuck and charged, so only `halt` halts. After `halt` the state
  stutters at no cost.
* Randomness is a tape `ω : ℕ → Bool` of independent fair coins (`coinTape`), one bit per executed `coin`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor carries a
function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]`.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`; the tape cursor advances.
* `deg d a`: `p[d] :=` the degree of node `p[a]` (one query).
* `nbr d a b`: `p[d] :=` the `p[b]`-th neighbor (0-based) of node `p[a]` (one query).
* `halt`: stop; the output is read from memory. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | coin (dst : ℕ)
  | deg (dst node : ℕ)
  | nbr (dst node index : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions `accept`/`reject` do not occur (the
machine stops only through `halt`). -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P`: extension instructions are placeholders here and are always dispatched by
`step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration (program counter, real registers, pointers, real memory), integer
memory, the coin-tape cursor, the halted flag, the work counter and the query counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  work : ℕ
  queries : ℕ

/-- A pointer value as a node of `Fin n`, if it is one. -/
def nodeOf (n : ℕ) (z : ℤ) : Option (Fin n) :=
  if h : 0 ≤ z ∧ z.toNat < n then some ⟨z.toNat, h.2⟩ else none

/-- The answer to a degree query on the pointer value `a`: the length of the adjacency list, or `−1`. -/
def degAnswer {n : ℕ} (nbrs : Fin n → List (Fin n)) (a : ℤ) : ℤ :=
  match nodeOf n a with
  | some v => ((nbrs v).length : ℤ)
  | none => -1

/-- The answer to a neighbor query on the pointer values `a`, `b`: the `b`-th entry (0-based) of the adjacency
list of node `a`, or `−1`. -/
def nbrAnswer {n : ℕ} (nbrs : Fin n → List (Fin n)) (a b : ℤ) : ℤ :=
  match nodeOf n a with
  | some v =>
    if 0 ≤ b then
      match (nbrs v)[b.toNat]? with
      | some u => ((u : ℕ) : ℤ)
      | none => -1
    else -1
  | none => -1

/-- One step of program `P` on the graph `nbrs` and the coin tape `ω`. Halted states stutter at no cost; every
other step costs one unit of work; oracle instructions also cost one query. -/
noncomputable def step (P : Program) {n : ℕ} (nbrs : Fin n → List (Fin n)) (ω : ℕ → Bool) (s : State) :
    State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.integerLoad d a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory := Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.coin d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d (if ω s.cursor then 1 else 0) } }
    | some (.deg d a) =>
        { t with
          queries := s.queries + 1
          core := { t.core with
            ptrs := Function.update s.core.ptrs d (degAnswer nbrs (s.core.ptrs a)) } }
    | some (.nbr d a b) =>
        { t with
          queries := s.queries + 1
          core := { t.core with
            ptrs := Function.update s.core.ptrs d (nbrAnswer nbrs (s.core.ptrs a) (s.core.ptrs b)) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀` on the graph `nbrs` and the coin tape `ω`. -/
noncomputable def run (P : Program) {n : ℕ} (nbrs : Fin n → List (Fin n)) (s₀ : State) (ω : ℕ → Bool)
    (t : ℕ) : State :=
  (step P nbrs ω)^[t] s₀

/-- The state at the start of a run: program counter, registers, pointers, cursor, work and queries all `0`;
integer memory holds the list `ints` from cell `0`, real memory the list `reals` from cell `0`, and every other
cell is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, false, 0, 0⟩

/-- The real output vector of length `n` of a state: entry `v` is real memory at address `−1 − v`. -/
def outVec (n : ℕ) (st : State) : Fin n → ℝ :=
  fun v => st.core.mem (-1 - ((v : ℕ) : ℤ))

/-- The fair-coin tape: the product of uniform measures on `Bool` over `ℕ`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

end LocalPush


