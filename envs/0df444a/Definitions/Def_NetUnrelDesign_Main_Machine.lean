-- Prove2me | Definitions.Def_NetUnrelDesign_Main_Machine
-- name    : NetUnrelDesign_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:08:53.464945+00:00
-- url     : https://prove2.me/theorems/0aaa292f-51e0-4422-aca7-34d9969c7969
-- title:
--   The randomized real RAM with an oracle instruction, charged runs and their law
-- statement:
--   The paper's algorithms are programs of a randomized real RAM. Its core is the published real pointer machine `SmaleNinth_RealRAM`: real registers, integer pointers, real memory addressed through pointers, exact $+,-,\times,\div$ (with $x/0=0$), comparisons and jumps. The extension adds pointer addition and subtraction, an integer memory (for $n$, $m$, $k$, edge endpoints and partition labels), a pointer-to-real cast, $\exp$, $\log$, $\sqrt{\cdot}$, a uniform $[0,1]$ draw, one **oracle instruction** and `halt`. There is no floor, no real-to-integer conversion, and no instruction acting on a whole graph, vector or matrix.
--
--   An **oracle interface** fixes the query and answer types, how a query is read from memory at a base address, and how the answer is written back there. An **oracle** maps a query and a tape of independent uniform numbers to an answer and its cost. Call number $j$ of a run reads its own tape, independent of the machine tape and of every other call ("fresh randomness"). The law of a run is the product of independent uniform laws on the machine tape and on all oracle tapes.
--
--   Each executed instruction costs $1$. An oracle call costs $1$ plus the cost the oracle reports. A program counter outside the program is stuck and charged, and after `halt` the state does not change and costs nothing. The **total work** of a run is therefore finite exactly when the run halts. Expected work and expected numbers of calls are integrals in $[0,\infty]$ under the law of the run. The run keeps a transcript of all oracle calls (query, answer). A program is **admissible** when its real literals are rational and it does not use the core `accept`/`reject` instructions.
--
--   **Formalization Note.** `log` is Lean's total logarithm ($\log 0=0$) and `sqrt` is $0$ on negatives; both are encodings, not hypotheses. Outputs are read from memory cells with negative addresses ($-1-i$), and the expected values are `lintegral`s. `OracleMeasurable` asks the oracle to be jointly measurable in its query and its tape. `OracleDeterministic` asks it not to use its tape.
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), §1.1 (p. 2, PDF 3: cost model, oracle with fresh randomness); shape of the published KramersHubbard_PartitionFunction_Machine (copied, not imported)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open scoped BigOperators ENNReal Classical

noncomputable section

namespace NetUnrelDesign.Main

/-!
# The randomized real RAM with an oracle instruction, its charged runs and their law

Mu-Xia Sun, *Fast Approximation Algorithms for Minimizing Network Unreliability* (2026),
doi:10.5281/zenodo.23914978, §1.1 (p. 2, PDF 3): "We count arithmetic operations, evaluations of
elementary functions, random draws, and graph operations"; the oracle `U(H; s, β)` is called "with
fresh randomness for every call", and its expected work counts in the total work.

* The scalar core is the published real pointer RAM `SmaleNinth.RAMInstr` (real registers, integer
  pointer registers, real memory `ℤ → ℝ` addressed through pointers, `+ − × ÷` with `x/0 = 0`, real
  literals, pointer set/copy/increment/decrement, jumps on `r ≤ 0` and `p ≤ p'`). Extensions:
  pointer `+`/`−`, an integer memory `ℤ → ℤ` (for `n, m, k`, edge endpoints and partition labels),
  a pointer-to-real cast, `exp`, `log`, `sqrt` (Lean's total `Real.log`, `log 0 = 0`, and
  `Real.sqrt`, `0` on negatives), a uniform `[0,1]` draw, one oracle instruction, and `halt`. There
  is no floor and no real-to-integer conversion, and no instruction acts on a whole graph, vector or
  matrix.
* An oracle interface `OracleSpec` fixes the query and answer types, the decoding of a query from
  memory at a base address (`none`: malformed, the instruction is then a charged no-op that makes no
  call) and the writing of an answer into memory at that address. An oracle is a map
  `Query → (ℕ → ℝ) → Answer × ℕ` from the query and a uniform tape to the answer and its cost; it is
  a fixed procedure that sees nothing but its query and its own tape.
* Call number `j` of a run reads its own tape `ω'_j`, independent of the machine tape `ω` and of
  every other call ("fresh randomness"). The sample space is `(ℕ → ℝ) × (ℕ → ℕ → ℝ)`, with the law
  `jointLaw`: independent uniform `[0,1]` coordinates throughout (`Measure.infinitePi`).
* Cost: every executed instruction costs `1`; an oracle call costs additionally the cost reported by
  the oracle. A program counter outside the program is stuck and charged `1` per step. After `halt`
  the state stutters at no cost. Hence `totalWork` (the supremum over time of the work counter) is
  finite exactly on halting runs and `∞` otherwise; `totalCalls` counts oracle calls the same way.
* The transcript records every oracle call (query, answer) in order.
* `Admissible P`: every real literal of the program is rational, and the core `accept`/`reject`
  instructions do not occur. This restricts the program, never the inputs.
-/

/-- An oracle interface: query and answer types (with measurable structures), how a query is read
from real and integer memory at a base address, and how an answer is written there. -/
structure OracleSpec where
  /-- Queries. -/
  Query : Type
  /-- Answers. -/
  Answer : Type
  /-- Measurable structure on queries. -/
  measQ : MeasurableSpace Query
  /-- Measurable structure on answers. -/
  measA : MeasurableSpace Answer
  /-- Read a query from (real memory, integer memory) at a base address; `none` if malformed. -/
  decode : (ℤ → ℝ) → (ℤ → ℤ) → ℤ → Option Query
  /-- Write an answer into (real memory, integer memory) at a base address. -/
  encode : Answer → (ℤ → ℝ) → (ℤ → ℤ) → ℤ → (ℤ → ℝ) × (ℤ → ℤ)

attribute [instance] OracleSpec.measQ OracleSpec.measA

/-- An oracle: answer and cost from a query and the call's own uniform tape. -/
abbrev Oracle (I : OracleSpec) := I.Query → (ℕ → ℝ) → I.Answer × ℕ

/-- The oracle is jointly measurable in its query and its tape. -/
def OracleMeasurable (I : OracleSpec) (O : Oracle I) : Prop :=
  Measurable fun p : I.Query × (ℕ → ℝ) => O p.1 p.2

/-- The oracle does not use its tape (a deterministic procedure). -/
def OracleDeterministic (I : OracleSpec) (O : Oracle I) : Prop :=
  ∀ q ω₁ ω₂, O q ω₁ = O q ω₂

/-- An instruction.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]`.
* `intLoad d a`, `intStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `exp d a`, `log d a`, `sqrt d a`: `r[d] := exp r[a]`, `log r[a]`, `sqrt r[a]`.
* `uniform d`: `r[d] :=` the next coordinate of the machine tape.
* `oracle q`: one oracle call with the query stored at base address `p[q]`; the answer is written at
  that address.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | intLoad (dst address : ℕ)
  | intStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | sqrt (dst src : ℕ)
  | uniform (dst : ℕ)
  | oracle (base : ℕ)
  | halt

/-- A program: one finite list of instructions. -/
abbrev Program := List Instr

/-- Every real literal is rational and the core halting instructions do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The core table of `P` (extension instructions are placeholders, dispatched by `step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: core configuration, integer memory, tape cursor, number of oracle calls,
transcript, halted flag and work counter. -/
structure State (I : OracleSpec) where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Integer memory. -/
  ints : ℤ → ℤ
  /-- Next unread coordinate of the machine tape. -/
  cursor : ℕ
  /-- Number of oracle calls made. -/
  calls : ℕ
  /-- The oracle calls made, in order. -/
  transcript : List (I.Query × I.Answer)
  /-- Halted flag. -/
  halted : Bool
  /-- Work: executed instructions plus oracle costs. -/
  work : ℕ

/-- One step of `P` with oracle `O`, machine tape `ω` and oracle tapes `ω'`. -/
def step {I : OracleSpec} (P : Program) (O : Oracle I) (ω : ℕ → ℝ) (ω' : ℕ → ℕ → ℝ)
    (s : State I) : State I :=
  if s.halted then s else
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some op =>
      let t : State I := { s with
        work := s.work + 1
        core := { s.core with pc := s.core.pc + 1 } }
      let setReg (d : ℕ) (v : ℝ) : State I :=
        { t with core := { t.core with regs := Function.update s.core.regs d v } }
      match op with
      | .core _ => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
      | .pointerAdd d a b =>
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
      | .pointerSub d a b =>
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
      | .intLoad d a =>
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs d (s.ints (s.core.ptrs a)) } }
      | .intStore a b => { t with ints := Function.update s.ints (s.core.ptrs a) (s.core.ptrs b) }
      | .pointerReal d a => setReg d (s.core.ptrs a : ℝ)
      | .exp d a => setReg d (Real.exp (s.core.regs a))
      | .log d a => setReg d (Real.log (s.core.regs a))
      | .sqrt d a => setReg d (Real.sqrt (s.core.regs a))
      | .uniform d => { setReg d (ω s.cursor) with cursor := s.cursor + 1 }
      | .oracle q =>
          match I.decode s.core.mem s.ints (s.core.ptrs q) with
          | none => t
          | some qu =>
            let r := O qu (ω' s.calls)
            let mi := I.encode r.1 s.core.mem s.ints (s.core.ptrs q)
            { t with
              work := s.work + 1 + r.2
              calls := s.calls + 1
              transcript := s.transcript ++ [(qu, r.1)]
              ints := mi.2
              core := { t.core with mem := mi.1 } }
      | .halt => { t with halted := true }

/-- The state after `t` steps from `s₀` on the sample point `ω = (machine tape, oracle tapes)`. -/
def run {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) (t : ℕ) : State I :=
  (step P O ω.1 ω.2)^[t] s₀

/-- Independent uniform `[0,1]` draws. -/
def uniformTape : MeasureTheory.Measure (ℕ → ℝ) :=
  MeasureTheory.Measure.infinitePi
    (fun _ : ℕ => (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))

/-- The law of a run: the machine tape and the oracle tapes, all independent uniform. -/
def jointLaw : MeasureTheory.Measure ((ℕ → ℝ) × (ℕ → ℕ → ℝ)) :=
  uniformTape.prod (MeasureTheory.Measure.infinitePi fun _ : ℕ => uniformTape)

/-- The start state: registers and pointers `0`, nothing called, integer memory holds `ints` from
cell `0`, real memory holds `reals` from cell `0`, every other cell is `0`. -/
def initState (I : OracleSpec) (ints : List ℤ) (reals : List ℝ) : State I :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, 0, [], false, 0⟩

/-- Total work of the run (`∞` on a non-halting run). -/
def totalWork {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) : ℝ≥0∞ :=
  ⨆ t, ((run P O s₀ ω t).work : ℝ≥0∞)

/-- Total number of oracle calls of the run. -/
def totalCalls {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) : ℝ≥0∞ :=
  ⨆ t, ((run P O s₀ ω t).calls : ℝ≥0∞)

/-- Total number of oracle calls whose query satisfies `p`. -/
def totalCallsWhere {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (p : I.Query → Prop) [DecidablePred p] (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) : ℝ≥0∞ :=
  ⨆ t, (((run P O s₀ ω t).transcript.filter fun c => p c.1).length : ℝ≥0∞)

/-- Expected total work. -/
def expectedWork {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I) : ℝ≥0∞ :=
  ∫⁻ ω, totalWork P O s₀ ω ∂jointLaw

/-- Expected number of oracle calls. -/
def expectedCalls {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I) : ℝ≥0∞ :=
  ∫⁻ ω, totalCalls P O s₀ ω ∂jointLaw

/-- The run halts, and its halted state satisfies `good`. -/
def HaltsWith {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (good : State I → Prop) (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) : Prop :=
  ∃ t, (run P O s₀ ω t).halted = true ∧ good (run P O s₀ ω t)

/-- Every halted state reached on every sample point satisfies `good`. -/
def OnEveryHalt {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (good : State I → Prop) : Prop :=
  ∀ ω t, (run P O s₀ ω t).halted = true → good (run P O s₀ ω t)

/-- Every state reached on every sample point satisfies `good` (used for transcript clauses). -/
def OnEveryState {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (good : State I → Prop) : Prop :=
  ∀ ω t, good (run P O s₀ ω t)

/-- The probability that the run does not halt in a state satisfying `good`. -/
def failureProb {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (good : State I → Prop) : ℝ≥0∞ :=
  jointLaw {ω | ¬ HaltsWith P O s₀ good ω}

/-- The halted state of the run (the start state if the run does not halt). -/
def finalState {I : OracleSpec} (P : Program) (O : Oracle I) (s₀ : State I)
    (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) : State I :=
  if h : ∃ t, (run P O s₀ ω t).halted = true then
    run P O s₀ ω (Classical.choose h) else s₀

/-- Real output cell `i` (address `−1 − i`). -/
def outReal {I : OracleSpec} (s : State I) (i : ℕ) : ℝ := s.core.mem (-1 - (i : ℤ))

/-- Integer output cell `i` (address `−1 − i`). -/
def outInt {I : OracleSpec} (s : State I) (i : ℕ) : ℤ := s.ints (-1 - (i : ℤ))

/-- The real output vector of length `d` starting at real output cell `off`. -/
def outVec {I : OracleSpec} (s : State I) (off d : ℕ) : Fin d → ℝ := fun i => outReal s (off + i)

/-- The `d × d` real output matrix, row-major, starting at real output cell `off`. -/
def outMat {I : OracleSpec} (s : State I) (off d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => outReal s (off + i * d + j)

/-- The no-oracle interface (every oracle instruction is malformed). -/
def noOracle : OracleSpec where
  Query := Empty
  Answer := Unit
  measQ := ⊤
  measA := ⊤
  decode := fun _ _ _ => none
  encode := fun _ mem ints _ => (mem, ints)

/-- The unique oracle of the no-oracle interface. -/
def noOracleFn : Oracle noOracle := fun q _ => q.elim

/-- Real vector cells of a list. -/
def vecList {d : ℕ} (v : Fin d → ℝ) : List ℝ := List.ofFn v

/-- Matrix cells, row-major. -/
def matList {r c : ℕ} (A : Fin r → Fin c → ℝ) : List ℝ := (List.ofFn fun i => List.ofFn (A i)).flatten

end NetUnrelDesign.Main


