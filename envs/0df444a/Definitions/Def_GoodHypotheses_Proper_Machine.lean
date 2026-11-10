-- Prove2me | Definitions.Def_GoodHypotheses_Proper_Machine
-- name    : GoodHypotheses_Proper_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:14:18.244944+00:00
-- url     : https://prove2.me/theorems/325b088c-492b-4003-a19d-0be08516e089
-- title:
--   The cost model: a unit-cost randomized real RAM with sample oracles for p and h_i and density oracles for h_i; the law of a run
-- statement:
--   The paper charges constant time for a sample from $p$ or any $h_i$ and for a density query $h_i(x)$, and counts samples from $p$; there is no density access to $p$ (pp. 1–2, §3). The machine is the published real-RAM core `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$, rational literals, indirect real memory, pointer registers, comparison jumps) extended with integer pointer arithmetic, an integer memory, a pointer-to-real cast, $\exp$, $\log$, a uniform tape, `halt`, and **domain registers** holding elements of $X$, touched only by `domCopy`, `sampleP` (next sample of $p$), `sampleH` (next sample of $h_{p[i]}$) and `evalH` (real register $:=h_{p[i]}(d)$). Every executed instruction costs one step; each `sampleP` counts one sample from $p$. A program is a list of instructions, fixed independently of $X$, $\mu$ and the densities; `Admissible` requires rational literals. `OracleFree` programs use no uniform draws and no domain registers (deterministic). The **tape** holds, independently, i.i.d. samples of $p$, for each $i$ i.i.d. samples of $h_i$, and i.i.d. Uniform$[0,1]$ values; the $k$-th draw of each kind reads the $k$-th cell, so the tape law is the law of fresh adaptive draws. Input: $n$ in integer memory cell 0 and $\varepsilon,\delta$ in real memory cells 0, 1; the output index (0-based) is pointer register 0 at halting, a real output is real memory cell $-1$.
--
--   **Formalization Note.** `tapeLaw` is the product of `Measure.infinitePi` measures. An out-of-range hypothesis index or an empty domain register makes `sampleH` empty the register and `evalH` return 0. An invalid program counter is stuck and charged, so only `halt` halts.
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), pp. 1–2 and §3 p. 13 (computational model)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace GoodHypotheses.Proper

/-!
# The cost model: a unit-cost randomized real RAM with sample and density oracles

Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, *A Good Way to Find Good Hypotheses*,
STOC 2027 submission (manuscript sha256 a428fbe0…), p. 2 and §3 p. 13: "We can draw a sample
from p or any h_i in constant time, and we can evaluate h_i(x) at any x ∈ X in constant time";
"The sample complexity s refers to the number of samples an algorithm takes from p".
There is no density access to `p`.

The paper names no machine. This one is the published core `SmaleNinth.RAMInstr` (exact
`+ − × ÷`, real literals, indirect real memory, pointer set/copy/increment/decrement, comparison
jumps), extended (pattern of the published `PureDPQR.Machine`) with:
* integer pointer addition/subtraction, an integer memory, a pointer-to-real cast;
* `exp` and `log` (unit cost; `log` is `Real.log`, so `log 0 = 0`; division by `0` is `0`);
* `unif`: the next cell of a tape of independent Uniform[0,1] values;
* **domain registers** `d[0], d[1], …` holding elements of `X` (initially empty). The only
  operations touching them are `domCopy`, `sampleP` (`d := ` the next independent sample of `p`),
  `sampleH` (`d := ` the next independent sample of `h_{p[i]}`) and `evalH` (`r := h_{p[i]}(d)`).
  Hypothesis indices are `0`-based pointer values; an index outside `[0, n)` or an empty domain
  register makes `sampleH` empty the register and `evalH` return `0`.
* `halt`.
No constructor carries a function or an element of `X`, so a program is fixed independently of
`X`, `μ`, the densities and the instance. There is no floor, no real-to-integer cast and no
pointer multiplication. `Admissible` requires rational literals and forbids the core's
`accept`/`reject`. Every executed instruction, oracle calls included, costs one step; an invalid
program counter is stuck and charged, so only `halt` halts. After halting the state stutters.

**Randomness** is a tape `ω = (Y, Z, U)`: `Y k` is the `k`-th sample of `p`, `Z (i, k)` the `k`-th
sample of `h_i`, `U k` the `k`-th uniform value. `tapeLaw` makes all cells independent, with laws
`p·μ`, `h_i·μ` and Uniform[0,1]. Each cell is read at most once, so this is the law of fresh
adaptive draws.
-/

/-- An instruction of the machine. -/
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
  /-- `d[dst] := d[src]` (domain registers). -/
  | domCopy (dst src : ℕ)
  /-- `d[dst] :=` the next sample from `p` (counts one sample from `p`). -/
  | sampleP (dst : ℕ)
  /-- `d[dst] :=` the next sample from `h_{p[index]}`. -/
  | sampleH (dst index : ℕ)
  /-- `r[dst] := h_{p[index]}(d[src])`. -/
  | evalH (dst index src : ℕ)
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

/-- The program is deterministic and oracle-free: no uniform draws, no domain-register
instruction (so no sample and no density query). -/
def OracleFree (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .unif _ | .domCopy _ _ | .sampleP _ | .sampleH _ _ | .evalH _ _ _ => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, never executed by
the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A random tape: samples of `p`, samples of each `h_i` (`(i, k) ↦` the `k`-th sample of `h_i`),
and uniform values. -/
abbrev Tape (X : Type*) (n : ℕ) : Type _ := (ℕ → X) × ((Fin n × ℕ) → X) × (ℕ → unitInterval)

/-- A machine state. -/
structure State (X : Type*) where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Integer memory. -/
  integerMemory : ℤ → ℤ
  /-- Domain registers (`none` = empty). -/
  dom : ℕ → Option X
  /-- Uniform-tape cursor. -/
  unifCursor : ℕ
  /-- Number of samples drawn from `p` so far (the cursor of `p`'s tape). -/
  pCursor : ℕ
  /-- Number of samples drawn from `h_i` so far, indexed by `i`. -/
  hCursor : ℕ → ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Number of instructions executed. -/
  work : ℕ

/-- One step of `P` with density oracles `h` and tape `ω`. -/
noncomputable def step {X : Type*} {n : ℕ} (P : Program) (h : Fin n → X → ℝ) (ω : Tape X n)
    (s : State X) : State X :=
  if s.halted then s else
    let t : State X := { s with
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
          unifCursor := s.unifCursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d ((ω.2.2 s.unifCursor : unitInterval) : ℝ) } }
    | some (.domCopy d a) => { t with dom := Function.update s.dom d (s.dom a) }
    | some (.sampleP d) =>
        { t with
          pCursor := s.pCursor + 1
          dom := Function.update s.dom d (some (ω.1 s.pCursor)) }
    | some (.sampleH d q) =>
        if hq : 0 ≤ s.core.ptrs q ∧ s.core.ptrs q < (n : ℤ) then
          { t with
            hCursor := Function.update s.hCursor (s.core.ptrs q).toNat
              (s.hCursor (s.core.ptrs q).toNat + 1)
            dom := Function.update s.dom d
              (some (ω.2.1 (⟨(s.core.ptrs q).toNat, by omega⟩, s.hCursor (s.core.ptrs q).toNat))) }
        else { t with dom := Function.update s.dom d none }
    | some (.evalH r q d) =>
        let value : ℝ :=
          if hq : 0 ≤ s.core.ptrs q ∧ s.core.ptrs q < (n : ℤ) then
            match s.dom d with
            | some x => h ⟨(s.core.ptrs q).toNat, by omega⟩ x
            | none => 0
          else 0
        { t with core := { t.core with regs := Function.update s.core.regs r value } }
    | some .halt => { t with halted := true }

/-- The state after `k` steps. -/
noncomputable def run {X : Type*} {n : ℕ} (P : Program) (h : Fin n → X → ℝ) (ω : Tape X n)
    (s₀ : State X) (k : ℕ) : State X :=
  (step P h ω)^[k] s₀

/-- The initial state: all registers, pointers, counters `0`, domain registers empty; integer
memory holds `ints` from cell `0`, real memory holds `reals` from cell `0`, other cells `0`. -/
noncomputable def initState (X : Type*) (ints : List ℤ) (reals : List ℝ) : State X :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, fun _ => none, 0, 0, fun _ => 0, false, 0⟩

/-- The run halts within `B` steps (instructions executed). -/
def HaltsWithin {X : Type*} {n : ℕ} (P : Program) (h : Fin n → X → ℝ) (ω : Tape X n)
    (s₀ : State X) (B : ℝ) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ B ∧ (run P h ω s₀ k).halted = true

/-- The run draws at most `B` samples from `p`, at every time. -/
def SamplesWithin {X : Type*} {n : ℕ} (P : Program) (h : Fin n → X → ℝ) (ω : Tape X n)
    (s₀ : State X) (B : ℝ) : Prop :=
  ∀ k : ℕ, ((run P h ω s₀ k).pCursor : ℝ) ≤ B

open Classical in
/-- The first halted state of the run, if the run halts. -/
noncomputable def finalState {X : Type*} {n : ℕ} (P : Program) (h : Fin n → X → ℝ)
    (ω : Tape X n) (s₀ : State X) : Option (State X) :=
  if hk : ∃ k, (run P h ω s₀ k).halted = true then some (run P h ω s₀ (Nat.find hk)) else none

/-- The output index: pointer register `0` at the first halted state, read as a `0`-based index
in `Fin n`; `none` if the run never halts or the value is outside `[0, n)`. -/
noncomputable def outIndex {X : Type*} {n : ℕ} (P : Program) (h : Fin n → X → ℝ) (ω : Tape X n)
    (s₀ : State X) : Option (Fin n) :=
  match finalState P h ω s₀ with
  | some s =>
      if hs : 0 ≤ s.core.ptrs 0 ∧ s.core.ptrs 0 < (n : ℤ) then
        some ⟨(s.core.ptrs 0).toNat, by omega⟩
      else none
  | none => none

/-- The real output: real memory cell `-1` at the first halted state, `0` if the run never
halts. -/
noncomputable def outReal {X : Type*} {n : ℕ} (P : Program) (h : Fin n → X → ℝ) (ω : Tape X n)
    (s₀ : State X) : ℝ :=
  match finalState P h ω s₀ with
  | some s => s.core.mem (-1)
  | none => 0

/-- The law of the tape: all cells independent; `Y k ∼ Pp` (the law with density `p`),
`Z (i, k) ∼ Ph i` (the law with density `h_i`), `U k ∼` Uniform[0,1]. -/
noncomputable def tapeLaw {X : Type*} [MeasurableSpace X] {n : ℕ} (Pp : ProbabilityMeasure X)
    (Ph : Fin n → ProbabilityMeasure X) : Measure (Tape X n) :=
  (Measure.infinitePi fun _ : ℕ => (Pp : Measure X)).prod
    ((Measure.infinitePi fun q : Fin n × ℕ => (Ph q.1 : Measure X)).prod
      (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))

/-- The input of the selection problem: integer memory cell `0` holds `n`; real memory cells
`0, 1` hold `ε, δ`. Densities and samples are reached only through the oracles. -/
noncomputable def selectionInput (X : Type*) (n : ℕ) (ε δ : ℝ) : State X :=
  initState X [(n : ℤ)] [ε, δ]

/-- The input of minimum-score selection (Fact 2.1): integer memory cell `0` holds `n`; real
memory cells `0, …, n − 1` hold `σ_1, …, σ_n`. -/
noncomputable def scoresInput (X : Type*) {n : ℕ} (σ : Fin n → ℝ) : State X :=
  initState X [(n : ℤ)] (List.ofFn σ)

/-- The input of weighted-quantile selection (Lemma C.1): integer memory cell `0` holds `n`;
real memory holds `λ` in cell `0`, `v_1, …, v_n` in cells `1, …, n` and `w_1, …, w_n` in cells
`n + 1, …, 2n`. -/
noncomputable def quantileInput (X : Type*) {n : ℕ} (v w : Fin n → ℝ) (lam : ℝ) : State X :=
  initState X [(n : ℤ)] (lam :: (List.ofFn v ++ List.ofFn w))

end GoodHypotheses.Proper


