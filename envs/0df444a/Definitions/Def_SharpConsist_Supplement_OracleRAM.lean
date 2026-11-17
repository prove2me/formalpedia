-- Prove2me | Definitions.Def_SharpConsist_Supplement_OracleRAM
-- name    : SharpConsist_Supplement_OracleRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:22:14.201298+00:00
-- url     : https://prove2.me/theorems/76526aae-01c6-44cf-a0f5-8f18ba136855
-- title:
--   Counted real-RAM oracle machine (§2.1)
-- statement:
--   The computation model of §2.1 counts unit-cost value queries and exact arithmetic, with exact sampling from the specified distributions. It is realized as a randomized real RAM with a value oracle:
--
--   1. the scalar core is the published real pointer machine `SmaleNinth.RAMInstr`: real registers, integer pointer registers, real memory addressed through pointers, exact $+,-,\times,\div$ (with $x/0=0$), real literals, pointer set/copy/increment/decrement, and jumps on $r\le0$ and $p\le p'$; there is no floor and no conversion from reals to integers;
--   2. `uniform` reads the next coordinate of a tape of independent Uniform$[0,1]$ values; categorical draws with computed real weights, uniform subsets and uniform positions are programs over it;
--   3. `query` makes one value query on the set $\{i<t: M[p+i]>0\}$ of current elements marked in memory, so every queried set is produced by the program;
--   4. `halt` ends the work for the current arrival and outputs the set of current elements marked in memory.
--
--   Every executed instruction costs one step; a value query is also counted as a query. Memory and the tape cursor persist between arrivals. At the start of each arrival the machine writes the number $t$ of arrived elements and the capacity $k$ into registers $0,1$ and resumes after its last `halt`. A program is **admissible** if its real literals are rational and it does not use the core's accept/reject. The online run fails if some arrival does not halt within its step budget. A static run is a single call on a current set of $n$ elements with capacity $\kappa$.
--
--   **Formalization Note** The tape law is the product of the uniform laws on $[0,1]$ (`Measure.infinitePi`). A program counter outside the program is stuck and charged.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §2.1, p.4

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace SharpConsist.Supplement.OracleRAM

/-!
# The counted real-RAM oracle machine of §2.1

Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held
version, sha256 874ec76c…), §2.1, p.4: "Each value query has unit cost … Our upper bounds use exact
arithmetic and exact sampling from the specified distributions. Algorithms must terminate almost
surely after every arrival on every valid instance."

The scalar core is the published real pointer RAM `SmaleNinth.RAMInstr` (real registers, integer
pointer registers, real memory `ℤ → ℝ` addressed through pointers, exact `+ − × ÷` with `x / 0 = 0`,
literals, pointer set/copy/increment/decrement, jumps on `r ≤ 0` and `p ≤ p'`). It has no floor and
no real-to-integer conversion. The extension adds:
* `uniform d`: `r[d] :=` the next coordinate of a tape of independent Uniform`[0,1]` values (exact
  sampling; categorical draws with computed real weights, uniform subsets and uniform window
  positions are programs over it);
* `query d q`: one value query, `r[d] := F(S)` for the set `S = {i < t : M[p[q] + i] > 0}` of current
  elements marked in memory from address `p[q]` (so the queried set is produced by the program);
* `halt q`: ends the work for the current arrival with output `{i < t : M[p[q] + i] > 0}`.

Every executed instruction costs one step; a value query is one step and is also counted as a
query. Registers, memory and the tape cursor persist between arrivals, so the algorithm may store
the whole history. At the start of the arrival that brings the number of arrived elements to `t`,
the machine writes `t` and the capacity `k` into real registers `0`, `1` and pointer registers `0`,
`1`, and resumes after its last `halt`. A program counter outside the program is stuck (charged);
the run of an arrival fails if it has not halted within its step budget.
-/

/-- An instruction: a `SmaleNinth` real-RAM instruction, a uniform draw, a value query, or the end of
the current arrival. -/
inductive Instr where
  | core (i : SmaleNinth.RAMInstr)
  | uniform (dst : ℕ)
  | query (dst q : ℕ)
  | halt (q : ℕ)

/-- A program: one finite list of instructions. -/
abbrev Program := List Instr

/-- Every real literal is rational and the core `accept`/`reject` do not occur (so no information
is hidden in a real constant). -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ c) => ∃ r : ℚ, c = (r : ℝ)
    | .core .accept => False
    | .core .reject => False
    | _ => True

/-- The core table of `P` (extension instructions are placeholders, dispatched by `step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration and the tape cursor. -/
structure State where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- The next unread tape coordinate. -/
  cursor : ℕ

/-- The set of current elements `{i < t : M[base + i] > 0}` marked in memory from `base`. -/
noncomputable def readSet (mem : ℤ → ℝ) (base : ℤ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter fun i => 0 < mem (base + i)

/-- The result of one step: continue (recording whether a query was made) or end the arrival. -/
inductive StepResult where
  | cont (s : State) (queried : Bool)
  | halted (s : State) (out : Finset ℕ)

/-- One step of `P` with value oracle `F`, `t` arrived elements and tape `ω`. -/
noncomputable def step (P : Program) (F : Finset ℕ → ℝ) (t : ℕ) (ω : ℕ → unitInterval)
    (s : State) : StepResult :=
  match P[s.core.pc]? with
  | none => .cont s false
  | some (.core _) => .cont { s with core := SmaleNinth.RAMStep (coreProgram P) s.core } false
  | some (.uniform d) =>
      .cont ⟨{ s.core with
        pc := s.core.pc + 1
        regs := Function.update s.core.regs d (ω s.cursor : ℝ) }, s.cursor + 1⟩ false
  | some (.query d q) =>
      .cont { s with core := { s.core with
        pc := s.core.pc + 1
        regs := Function.update s.core.regs d (F (readSet s.core.mem (s.core.ptrs q) t)) } } true
  | some (.halt q) =>
      .halted { s with core := { s.core with pc := s.core.pc + 1 } }
        (readSet s.core.mem (s.core.ptrs q) t)

/-- The work of one arrival with a budget of `fuel` steps, from state `s` with `q` queries made so far:
`some (state, output, number of queries)` if it halts within the budget, `none` otherwise. -/
noncomputable def runArrival (P : Program) (F : Finset ℕ → ℝ) (t : ℕ) (ω : ℕ → unitInterval) :
    ℕ → State → ℕ → Option (State × Finset ℕ × ℕ)
  | 0, _, _ => none
  | fuel + 1, s, q =>
    match step P F t ω s with
    | .halted s' out => some (s', out, q)
    | .cont s' b => runArrival P F t ω fuel s' (if b then q + 1 else q)

/-- The input written at the start of an arrival: `t` and `k` in real and pointer registers `0`, `1`. -/
def startArrival (s : State) (t k : ℕ) : State :=
  { s with core := { s.core with
      regs := Function.update (Function.update s.core.regs 0 (t : ℝ)) 1 (k : ℝ)
      ptrs := Function.update (Function.update s.core.ptrs 0 (t : ℤ)) 1 (k : ℤ) } }

/-- The initial state: everything `0`. -/
def initState : State := ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, 0⟩

/-- The online run on the first `t` arrivals with capacity `k` and per-arrival step budget `b`:
the final state and, per arrival, the output and the number of queries; `none` if some arrival
exceeds its budget. -/
noncomputable def runOnline (P : Program) (F : Finset ℕ → ℝ) (k : ℕ) (b : ℕ → ℕ)
    (ω : ℕ → unitInterval) : ℕ → Option (State × List (Finset ℕ × ℕ))
  | 0 => some (initState, [])
  | t + 1 =>
    match runOnline P F k b ω t with
    | none => none
    | some (s, h) =>
      match runArrival P F (t + 1) ω (b (t + 1)) (startArrival s (t + 1) k) 0 with
      | none => none
      | some (s', out, q) => some (s', h ++ [(out, q)])

/-- The output after arrival `i` recorded in a run history (`∅` for `i = 0`). -/
def outputAt (h : List (Finset ℕ × ℕ)) : ℕ → Finset ℕ
  | 0 => ∅
  | i + 1 => (h[i]?.map Prod.fst).getD ∅

/-- The number of queries at arrival `i ≥ 1` recorded in a run history. -/
def queriesAt (h : List (Finset ℕ × ℕ)) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (h[i]?.map Prod.snd).getD 0

/-- The maintained set `S_t` of the online run (`∅` if the run failed). -/
noncomputable def outAt (P : Program) (F : Finset ℕ → ℝ) (k : ℕ) (b : ℕ → ℕ)
    (ω : ℕ → unitInterval) (t : ℕ) : Finset ℕ :=
  match runOnline P F k b ω t with
  | some (_, h) => outputAt h t
  | none => ∅

/-- A static run (one call on a current set of `n` elements with capacity `κ`, step budget `b`). -/
noncomputable def runStatic (P : Program) (F : Finset ℕ → ℝ) (n κ b : ℕ) (ω : ℕ → unitInterval) :
    Option (State × Finset ℕ × ℕ) :=
  runArrival P F n ω b (startArrival initState n κ) 0

/-- The output of a static run (`∅` if the run failed). -/
noncomputable def staticOut (P : Program) (F : Finset ℕ → ℝ) (n κ b : ℕ) (ω : ℕ → unitInterval) :
    Finset ℕ :=
  match runStatic P F n κ b ω with
  | some (_, A, _) => A
  | none => ∅

/-- The law of the tape: independent Uniform`[0,1]` coordinates. -/
noncomputable def tape : MeasureTheory.Measure (ℕ → unitInterval) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ => (MeasureTheory.volume : MeasureTheory.Measure unitInterval)

end SharpConsist.Supplement.OracleRAM


