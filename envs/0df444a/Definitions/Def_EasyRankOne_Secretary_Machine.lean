-- Prove2me | Definitions.Def_EasyRankOne_Secretary_Machine
-- name    : EasyRankOne_Secretary_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:05:40.481687+00:00
-- url     : https://prove2.me/theorems/5e4567a2-b861-48e0-b58a-c44622aab4ac
-- title:
--   The online oracle machine: unit-cost randomized real RAM with arrival, comparison and independence instructions (§2.2, §6)
-- statement:
--   The cost model of the goal. The paper (p. 22) works in "the randomized real RAM: exact arithmetic operations, comparisons, and independent uniform draws from $[0,1]$ cost one unit each, as do evaluations of $\ln$ and $\exp$ … Independence queries are counted separately", in the secretary model of p. 6: the $n=|V|$ elements arrive in a uniformly random order, each must be irrevocably accepted or rejected before the next arrival, the accepted set must be independent, $n$ is known, and independence queries may involve only observed elements; an ordinal algorithm uses values only through their tie-broken order.
--
--   A **program** is a finite list of instructions: the instructions of the published real-RAM core `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$, real literals, indirect real memory, pointer registers, comparison jumps), integer pointer arithmetic and an integer memory, $\exp$, $\log$, `unif` (the next cell of a tape of i.i.d. Uniform$(0,1)$ values), and the online instructions. Elements are known to the program only by their **arrival index** $0,1,\dots$:
--   - `arrive d` waits for the next arrival and writes its arrival index (allowed only when every earlier arrival is decided and fewer than $n$ have arrived);
--   - `cmp d i j` writes $1$ if arrival $i$ is larger than arrival $j$ in the tie-broken value order, else $0$ — the only access to values;
--   - `indep d len base` writes $1$ if the set of arrivals whose indices are listed in integer memory is independent in $M$, else $0$, and counts one independence query;
--   - `accept` / `reject` decide the current arrival; `halt` is allowed only once all $n$ elements have arrived and been decided.
--   A comparison or query on an index that has not arrived, a decision with no pending arrival, an early `arrive` or `halt` are **invalid**: the run stops with an invalid flag. The input is $n$ in integer memory cell $0$; the program never sees labels, values, the matroid or the arrival order. Every executed instruction costs one unit (`work`). For an arrival order $\pi$ (a bijection from arrival positions to $V$) and a tape $\omega$, `ALG` is the set of elements whose arrival was accepted, `totalWork` and `totalQueries` are the total numbers of instructions and independence queries (total work is $\infty$ for a run that never halts; the query count may remain finite), `runProb` and `runExp` are probability and expectation over $\pi$ uniform among the $n!$ bijections and, independently, the uniform tape.
--
--   **Formalization Note.** `Admissible P` requires rational literals and forbids the core's `accept`/`reject`. An invalid program counter is stuck and charged, so a run halts only through `halt` or an invalid instruction; after halting the state stutters at no cost. `log` is `Real.log` and division by $0$ gives $0$. `runProb E` averages over the $n!$ arrival orders the tape measure of $\{\omega: E(\pi,\omega)\}$; `runExp f` averages $\int^- f\,d(\text{tape})$ in $[0,\infty]$.
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 6, §2.2 (Model); p. 22, §6 (Computational model); p. 23, Theorem 6.1

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_EasyRankOne_Secretary_Greedy

open MeasureTheory
open scoped ENNReal

/-!
# The online oracle machine: a unit-cost randomized real RAM in the secretary model

Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, *As Easy as Rank One*, STOC 2027 submission
(manuscript of November 2026, sha256 f74f3f91…), §2.2 p. 6 (secretary model), §6 p. 22
(computational model), Theorem 6.1 p. 23.

"We work in the randomized real RAM: exact arithmetic operations, comparisons, and independent
uniform draws from [0, 1] cost one unit each, as do evaluations of ln and exp … Independence
queries are counted separately." "The n = |V| elements arrive in a uniformly random order. On
each arrival, the algorithm … must irrevocably accept or reject it before the next arrival. The
accepted set must be independent. The number n is known; values and the matroid are otherwise
unknown, and independence queries may involve only observed elements. … An algorithm is ordinal
if it uses values only through their tie-broken order."

The paper names no concrete machine. This one is the published core `SmaleNinth.RAMInstr`
(exact `+ − × ÷`, real literals, indirect real memory, pointer set/copy/increment/decrement,
comparison jumps), extended (pattern of the published `BayesOptStop.Scheme.Instr`) with
* integer pointer addition/subtraction, an integer memory, a pointer-to-real cast;
* `exp` and `log` (`log` is `Real.log`; division by `0` is `0`);
* `unif`: the next cell of a tape of independent Uniform(0,1) values;
* the online instructions. Elements are known to the program only by their **arrival index**
  `0, 1, …` (never by label, value or matroid data):
  - `arrive d`: wait for the next arrival; `p[d] :=` its arrival index. Allowed only when every
    earlier arrival has been decided and fewer than `n` elements have arrived.
  - `cmp d i j`: `p[d] := 1` if arrival `p[i]` is larger than arrival `p[j]` in the tie-broken
    value order, else `0` (the only access to values: ordinal).
  - `indep d len base`: `p[d] := 1` if the set of arrivals whose indices are stored in integer
    memory cells `p[base], …, p[base] + p[len] − 1` is independent in `M`, else `0`; counted as one
    independence query.
  - `accept` / `reject`: the irrevocable decision on the current (latest, undecided) arrival.
  - `halt`: allowed only when all `n` elements have arrived and been decided.
  `cmp`/`indep` on an index that has not arrived, a decision with no undecided arrival, an
  `arrive` before the current arrival is decided or after the `n`-th, and an early `halt` are
  **invalid**: the run stops with the flag `invalid` set.

Every executed instruction costs one unit (`work`); independence queries are also counted in
`queries`. An invalid program counter is stuck and charged, so a run halts only through `halt` or
an invalid instruction; after halting the state stutters at no cost. The input is `n` in integer
memory cell `0`; all other memory is `0`. `Admissible` requires rational literals and forbids
the core's `accept`/`reject`.
-/

namespace EasyRankOne.Secretary

/-- An instruction of the online oracle machine. -/
inductive Instr where
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `p[dst] := p[a] + p[b]`. -/
  | pointerAdd (dst a b : ℕ)
  /-- `p[dst] := p[a] - p[b]`. -/
  | pointerSub (dst a b : ℕ)
  /-- `p[dst] := I[p[address]]` (integer memory). -/
  | integerLoad (dst address : ℕ)
  /-- `I[p[address]] := p[src]`. -/
  | integerStore (address src : ℕ)
  /-- `r[dst] := (p[pointer] : ℝ)`. -/
  | pointerReal (dst pointer : ℕ)
  /-- `r[dst] := exp r[src]`. -/
  | exp (dst src : ℕ)
  /-- `r[dst] := log r[src]`. -/
  | log (dst src : ℕ)
  /-- `r[dst] :=` the next uniform tape value. -/
  | unif (dst : ℕ)
  /-- `p[dst] :=` the arrival index of the next arrival. -/
  | arrive (dst : ℕ)
  /-- `p[dst] := 1` if arrival `p[i]` is larger than arrival `p[j]`, else `0`. -/
  | cmp (dst i j : ℕ)
  /-- `p[dst] := 1` if the arrivals listed at `p[base]`, length `p[len]`, are independent. -/
  | indep (dst len base : ℕ)
  /-- Accept the current arrival. -/
  | accept
  /-- Reject the current arrival. -/
  | reject
  /-- Halt. -/
  | halt

/-- A program: one finite list of instructions. -/
abbrev Program := List Instr

/-- Every real literal is rational and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, never executed by
the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state. Arrivals are numbered `0, 1, …` in arrival order; `arrived` of them have
arrived, the first `decided` of them have been decided, `accepted` holds the accepted arrival
indices. -/
structure State where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Integer memory. -/
  integerMemory : ℤ → ℤ
  /-- Tape cursor. -/
  cursor : ℕ
  /-- Number of arrivals so far. -/
  arrived : ℕ
  /-- Number of arrivals decided so far. -/
  decided : ℕ
  /-- Arrival indices of the accepted arrivals. -/
  accepted : Finset ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Set when the run executed an invalid instruction. -/
  invalid : Bool
  /-- Number of instructions executed. -/
  work : ℕ
  /-- Number of independence queries made. -/
  queries : ℕ

/-- The list of integers stored in integer memory from cell `p[base]`, of length `p[len]`. -/
def readList (s : State) (len base : ℕ) : List ℤ :=
  List.ofFn fun i : Fin (s.core.ptrs len).toNat => s.integerMemory (s.core.ptrs base + (i : ℤ))

section Instance

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The set of elements whose arrival indices are listed in `L`, under the arrival order `π`
(arrival index `k ↦` element `π k`). -/
def arrivalSet (π : Fin (Fintype.card α) ≃ α) (L : List ℤ) : Set α :=
  {a | ∃ k : Fin (Fintype.card α), ((k : ℕ) : ℤ) ∈ L ∧ π k = a}

/-- The integer `i` is the arrival index of an element that has arrived in state `s`. -/
def Arrived (s : State) (i : ℤ) : Prop := 0 ≤ i ∧ i < (s.arrived : ℤ)

open Classical in
/-- One step of `P` on the instance `(M, v)` with arrival order `π` and uniform tape `ω`. -/
noncomputable def step (M : Matroid α) (v : α → ℝ) (π : Fin (Fintype.card α) ≃ α)
    (P : Program) (ω : ℕ → ℝ) (s : State) : State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    let bad : State := { s with work := s.work + 1, halted := true, invalid := true }
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
        { t with integerMemory :=
            Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.exp d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.exp (s.core.regs a)) } }
    | some (.log d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.log (s.core.regs a)) } }
    | some (.unif d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with regs := Function.update s.core.regs d (ω s.cursor) } }
    | some (.arrive d) =>
        if s.decided = s.arrived ∧ s.arrived < Fintype.card α then
          { t with
            arrived := s.arrived + 1
            core := { t.core with
              ptrs := Function.update s.core.ptrs d (s.arrived : ℤ) } }
        else bad
    | some (.cmp d i j) =>
        if Arrived s (s.core.ptrs i) ∧ Arrived s (s.core.ptrs j) then
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs d
                (if ∃ a b : Fin (Fintype.card α), ((a : ℕ) : ℤ) = s.core.ptrs i ∧
                    ((b : ℕ) : ℤ) = s.core.ptrs j ∧ Larger v (π a) (π b) then 1 else 0) } }
        else bad
    | some (.indep d len base) =>
        if ∀ i ∈ readList s len base, Arrived s i then
          { t with
            queries := s.queries + 1
            core := { t.core with
              ptrs := Function.update s.core.ptrs d
                (if M.Indep (arrivalSet π (readList s len base)) then 1 else 0) } }
        else bad
    | some .accept =>
        if s.decided < s.arrived then
          { t with decided := s.decided + 1, accepted := insert s.decided s.accepted }
        else bad
    | some .reject =>
        if s.decided < s.arrived then { t with decided := s.decided + 1 } else bad
    | some .halt =>
        if s.arrived = Fintype.card α ∧ s.decided = Fintype.card α then
          { t with halted := true }
        else bad

/-- The initial state: integer memory cell `0` holds `n`; everything else is `0`/empty. -/
def initState (n : ℕ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun z => if z = 0 then (n : ℤ) else 0,
    0, 0, 0, ∅, false, false, 0, 0⟩

/-- The state after `k` steps of `P` on the instance, from the input `n = |V|`. -/
noncomputable def run (M : Matroid α) (v : α → ℝ) (π : Fin (Fintype.card α) ≃ α)
    (P : Program) (ω : ℕ → ℝ) (k : ℕ) : State :=
  (step M v π P ω)^[k] (initState (Fintype.card α))

/-- The run never executes an invalid instruction. -/
def RunValid (M : Matroid α) (v : α → ℝ) (π : Fin (Fintype.card α) ≃ α) (P : Program)
    (ω : ℕ → ℝ) : Prop :=
  ∀ k, (run M v π P ω k).invalid = false

/-- The run halts. -/
def RunHalts (M : Matroid α) (v : α → ℝ) (π : Fin (Fintype.card α) ≃ α) (P : Program)
    (ω : ℕ → ℝ) : Prop :=
  ∃ k, (run M v π P ω k).halted = true

/-- The accepted set `ALG` of the run: the elements whose arrival was accepted at some step
(accepted indices are never removed). -/
def acceptedAt (π : Fin (Fintype.card α) ≃ α) (s : State) : Set α :=
  {a | ∃ k : Fin (Fintype.card α), (k : ℕ) ∈ s.accepted ∧ π k = a}

/-- `ALG` of the whole run. -/
noncomputable def ALG (M : Matroid α) (v : α → ℝ) (π : Fin (Fintype.card α) ≃ α)
    (P : Program) (ω : ℕ → ℝ) : Set α :=
  ⋃ k, acceptedAt π (run M v π P ω k)

/-- The total number of executed instructions (`⊤` if the run never halts). -/
noncomputable def totalWork (M : Matroid α) (v : α → ℝ) (π : Fin (Fintype.card α) ≃ α)
    (P : Program) (ω : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ k, ((run M v π P ω k).work : ℝ≥0∞)

/-- The total number of independence queries. -/
noncomputable def totalQueries (M : Matroid α) (v : α → ℝ) (π : Fin (Fintype.card α) ≃ α)
    (P : Program) (ω : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ k, ((run M v π P ω k).queries : ℝ≥0∞)

end Instance

/-- The uniform tape: independent Uniform(0,1) values. -/
noncomputable def uniformTape : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- A tape in the support: every cell in `(0,1)`. -/
def TapeInSupport (ω : ℕ → ℝ) : Prop :=
  ∀ i, ω i ∈ Set.Ioo (0 : ℝ) 1

section Law

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Probability of an event of the run under the uniform arrival order (uniform over the `n!`
bijections `Fin n ≃ α`) and, independently, the uniform tape. -/
noncomputable def runProb (E : (Fin (Fintype.card α) ≃ α) → (ℕ → ℝ) → Prop) : ℝ :=
  (Fintype.card (Fin (Fintype.card α) ≃ α) : ℝ)⁻¹ *
    ∑ π : Fin (Fintype.card α) ≃ α, (uniformTape {ω | E π ω}).toReal

/-- Expectation of a nonnegative extended-real quantity of the run under the same law. -/
noncomputable def runExp (f : (Fin (Fintype.card α) ≃ α) → (ℕ → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  (Fintype.card (Fin (Fintype.card α) ≃ α) : ℝ≥0∞)⁻¹ *
    ∑ π : Fin (Fintype.card α) ≃ α, ∫⁻ ω, f π ω ∂uniformTape

end Law

end EasyRankOne.Secretary


