-- Prove2me | Definitions.Def_DataDepProb_Discrete_Machine
-- name    : DataDepProb_Discrete_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:09:51.55938+00:00
-- url     : https://prove2.me/theorems/0259a267-3347-4898-8b2d-75fca1168762
-- title:
--   A unit-cost randomized real RAM with exp, log, uniform integer draws and a $\mathcal G$-evaluation oracle charged $d$ steps
-- statement:
--   The paper counts arithmetic operations, evaluations of exponentials and logarithms, and evaluations of the query mapping $\mathcal G$, but names no machine. This definition fixes one: the published real-RAM core `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$, real literals, indirect real memory, pointer registers with set, copy, increment, decrement, and comparison jumps), extended with
--   * pointer addition and subtraction, an integer memory, and a pointer-to-real cast;
--   * $\exp$ and $\log$ at unit cost;
--   * `unifNat`: a uniform integer in $\{0,\dots,m-1\}$, $m$ a pointer register, drawn from the next cell of a tape of independent Uniform$[0,1]$ values;
--   * `evalG`: reads a sample $s\in[d]^n$ from $n$ consecutive integer cells and writes the vector $(\mathcal G(s)(x))_{x\in[d]}$ into $d$ consecutive real cells; each call counts as one evaluation of $\mathcal G$ and is charged $d$ steps;
--   * `halt`.
--
--   No instruction carries a function, so $\mathcal G$ is reachable only through `evalG` and the unknown distribution not at all. A program is **admissible** if its real literals are rational and it does not use the core's accept/reject; it is **oracle-free** if it uses neither `unifNat` nor `evalG`. A run charges one step per instruction (`evalG`: $d$); the state also records the number of evaluations of $\mathcal G$ and the memory cells written. The estimator's input holds $n,d$ in pointer registers $0,1$ and the sample (entries $0,\dots,d-1$) in integer cells $0,\dots,n-1$; its output is real register $0$ at the first halted state. A vector output of length $d$ is read from real memory cells $0,\dots,d-1$. The tape law makes all tape cells independent and uniform on $[0,1]$.
--
--   **Formalization Note.** Division by $0$ gives $0$ and $\log 0=0$, as in Lean. An invalid program counter is stuck and charged, so only `halt` halts. `detG` and `zeroTape` are the trivial oracle and tape used to run oracle-free programs.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 2, Theorem 1.1 (evaluations of 𝒢, time); p. 11, §5 (one evaluation of 𝒢); p. 37, Appendix C (operation count)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace DataDepProb.Discrete

/-!
# The cost model: a unit-cost randomized real RAM with a `𝒢`-evaluation oracle

Feldman, Kale, Majid, Talwar, *Data-Dependent Probability Estimation via Sample Amplification*,
STOC 2027 submission (manuscript sha256 28400f1c…), p. 2 ("explicit randomized estimator",
"evaluations of 𝒢", "time"), §5 p. 11 ("We count one evaluation of 𝒢 as obtaining the vector
(𝒢(s)(x))_{x∈[d]} for a sample s ∈ [d]^n"), Appendix C p. 37 ("We count arithmetic operations and
evaluations of exponentials and logarithms").

The paper names no machine. This one is the published core `SmaleNinth.RAMInstr` (exact
`+ − × ÷`, real literals, indirect real memory, pointer set/copy/increment/decrement, comparison
jumps), extended (pattern of the published `GoodHypotheses.Proper` machine) with:
* integer pointer addition/subtraction, an integer memory, a pointer-to-real cast;
* `exp` and `log` (unit cost; `log` is `Real.log`, so `log 0 = 0`; division by `0` is `0`);
* `unifNat dst bound`: `p[dst] :=` a uniform integer in `{0, …, p[bound] − 1}` (`0` if
  `p[bound] ≤ 0`), computed from the next cell `U` of a tape of independent Uniform[0,1] values as
  `min(⌊m U⌋, m − 1)`, `m = p[bound]`; unit cost;
* `evalG src dst`: reads a sample `s ∈ [d]^n` from integer memory cells
  `p[src], …, p[src] + n − 1` (entries `0, …, d − 1`, the 0-based encoding of `[d]`) and writes
  `𝒢(s)(x)` into real memory cells `p[dst] + x`, `x = 0, …, d − 1`. If some cell is outside
  `{0, …, d − 1}`, it writes `0` there instead. Each call counts as one evaluation of `𝒢` and
  is charged `d` steps;
* `halt`.
No constructor carries a function: `𝒢` is reachable only through `evalG`, and the distribution
`D` not at all. `Admissible` requires rational literals and forbids the core's `accept`/`reject`.
Every executed instruction costs one step (`evalG` costs `d`); an invalid program counter is stuck
and charged, so only `halt` halts. After halting the state stutters.

**Input and output.** `initState ptrs ints reals`: pointer registers, integer memory (from cell
`0`) and real memory (from cell `0`) hold the given lists, everything else is `0`. The estimator's
input (`estimatorInput`) is `n, d` in pointer registers `0, 1` and the sample in integer cells
`0, …, n − 1`; its output is real register `0` at the first halted state. A vector output of
length `d` is read from real memory cells `0, …, d − 1` at the first halted state.

**Randomness** is a tape `ω : ℕ → [0, 1]`; `tapeLaw` makes its cells independent Uniform[0,1].
Each cell is read at most once, so the draws of `unifNat` are independent and uniform.

**Space.** The state records the set of real and integer memory cells written so far.
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
  /-- `p[dst] :=` a uniform integer in `{0, …, p[bound] − 1}` from the next tape cell. -/
  | unifNat (dst bound : ℕ)
  /-- `M[p[dst] + x] := 𝒢(s)(x)` for `x ∈ [d]`, `s` read from `I[p[src]], …, I[p[src] + n − 1]`. -/
  | evalG (src dst : ℕ)
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

/-- The program is deterministic and oracle-free: no `unifNat` and no `evalG`. -/
def OracleFree (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .unifNat _ _ | .evalG _ _ => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, never executed by
the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A random tape: independent Uniform[0,1] cells. -/
abbrev Tape : Type := ℕ → unitInterval

/-- A machine state. -/
structure State where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Integer memory. -/
  integerMemory : ℤ → ℤ
  /-- Uniform-tape cursor. -/
  unifCursor : ℕ
  /-- Number of evaluations of `𝒢` so far. -/
  evals : ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Number of steps charged so far. -/
  work : ℕ
  /-- Real memory cells written so far. -/
  realWritten : Finset ℤ
  /-- Integer memory cells written so far. -/
  intWritten : Finset ℤ

open Classical in
/-- The sample stored in integer memory cells `base, …, base + n − 1`, if every entry lies in
`{0, …, d − 1}`. -/
noncomputable def readSample (n d : ℕ) (mem : ℤ → ℤ) (base : ℤ) : Option (Fin n → Fin d) :=
  if h : ∀ i : Fin n, 0 ≤ mem (base + i) ∧ mem (base + i) < d then
    some fun i => ⟨(mem (base + i)).toNat, by have := h i; omega⟩
  else none

/-- The real memory after `evalG`: cells `base + x`, `x < d`, receive `𝒢(s)(x)` (or `0` if the
stored sample is invalid); other cells are unchanged. -/
noncomputable def writeG {n d : ℕ} (G : (Fin n → Fin d) → Fin d → ℝ) (smp : Option (Fin n → Fin d))
    (base : ℤ) (mem : ℤ → ℝ) : ℤ → ℝ :=
  fun z =>
    if h : base ≤ z ∧ z < base + d then
      match smp with
      | some s => G s ⟨(z - base).toNat, by omega⟩
      | none => 0
    else mem z

/-- The uniform integer in `{0, …, m − 1}` obtained from a tape value `u ∈ [0, 1]`
(`0` if `m ≤ 0`). -/
noncomputable def unifIndex (m : ℤ) (u : unitInterval) : ℤ :=
  if 0 < m then min (Int.floor ((m : ℝ) * (u : ℝ))) (m - 1) else 0

/-- The real memory cell written by a core instruction, if any. -/
def coreWrite (i : SmaleNinth.RAMInstr) (c : SmaleNinth.RAMConfig) : Finset ℤ :=
  match i with
  | .store q _ => {c.ptrs q}
  | _ => ∅

/-- One step of `P` with query mapping `G` (sample size `n`, domain size `d`) and tape `ω`. -/
noncomputable def step {n d : ℕ} (P : Program) (G : (Fin n → Fin d) → Fin d → ℝ) (ω : Tape)
    (s : State) : State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core i) =>
        { t with
          core := SmaleNinth.RAMStep (coreProgram P) s.core
          realWritten := s.realWritten ∪ coreWrite i s.core }
    | some (.pointerAdd dst a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub dst a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.core.ptrs a - s.core.ptrs b) } }
    | some (.integerLoad dst a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with
          integerMemory := Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b)
          intWritten := insert (s.core.ptrs a) s.intWritten }
    | some (.pointerReal dst a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (s.core.ptrs a : ℝ) } }
    | some (.exp dst a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (Real.exp (s.core.regs a)) } }
    | some (.log dst a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (Real.log (s.core.regs a)) } }
    | some (.unifNat dst bound) =>
        { t with
          unifCursor := s.unifCursor + 1
          core := { t.core with
            ptrs := Function.update s.core.ptrs dst
              (unifIndex (s.core.ptrs bound) (ω s.unifCursor)) } }
    | some (.evalG src dst) =>
        { t with
          work := s.work + d
          evals := s.evals + 1
          core := { t.core with
            mem := writeG G (readSample n d s.integerMemory (s.core.ptrs src))
              (s.core.ptrs dst) s.core.mem }
          realWritten := s.realWritten ∪
            (Finset.Ico (s.core.ptrs dst) (s.core.ptrs dst + d)) }
    | some .halt => { t with halted := true }

/-- The state after `k` steps. -/
noncomputable def run {n d : ℕ} (P : Program) (G : (Fin n → Fin d) → Fin d → ℝ) (ω : Tape)
    (s₀ : State) (k : ℕ) : State :=
  (step P G ω)^[k] s₀

/-- The initial state: pointer registers, integer memory and real memory hold the given lists
from index/cell `0`; everything else is `0`; no cell is marked written. -/
noncomputable def initState (ptrs : List ℤ) (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun i => ptrs.getD i 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, 0, false, 0, ∅, ∅⟩

/-- The input of the estimator: pointer registers `0, 1` hold `n, d`; integer memory cells
`0, …, n − 1` hold the sample, entry `x ∈ Fin d` stored as the integer `x`. -/
noncomputable def estimatorInput {n d : ℕ} (S : Fin n → Fin d) : State :=
  initState [(n : ℤ), (d : ℤ)] (List.ofFn fun i => ((S i : ℕ) : ℤ)) []

/-- The run halts with at most `B` steps charged. -/
def HaltsWithin {n d : ℕ} (P : Program) (G : (Fin n → Fin d) → Fin d → ℝ) (ω : Tape)
    (s₀ : State) (B : ℝ) : Prop :=
  ∃ k : ℕ, (run P G ω s₀ k).halted = true ∧ ((run P G ω s₀ k).work : ℝ) ≤ B

/-- The run makes at most `B` evaluations of `𝒢`, at every time. -/
def EvalsWithin {n d : ℕ} (P : Program) (G : (Fin n → Fin d) → Fin d → ℝ) (ω : Tape)
    (s₀ : State) (B : ℝ) : Prop :=
  ∀ k : ℕ, ((run P G ω s₀ k).evals : ℝ) ≤ B

/-- The run writes at most `B` distinct memory cells (real and integer), at every time. -/
def SpaceWithin {n d : ℕ} (P : Program) (G : (Fin n → Fin d) → Fin d → ℝ) (ω : Tape)
    (s₀ : State) (B : ℝ) : Prop :=
  ∀ k : ℕ, (((run P G ω s₀ k).realWritten.card + (run P G ω s₀ k).intWritten.card : ℕ) : ℝ) ≤ B

open Classical in
/-- The first halted state of the run, if the run halts. -/
noncomputable def finalState {n d : ℕ} (P : Program) (G : (Fin n → Fin d) → Fin d → ℝ)
    (ω : Tape) (s₀ : State) : Option State :=
  if hk : ∃ k, (run P G ω s₀ k).halted = true then some (run P G ω s₀ (Nat.find hk)) else none

/-- The real output: real register `0` at the first halted state, `0` if the run never halts. -/
noncomputable def outReal {n d : ℕ} (P : Program) (G : (Fin n → Fin d) → Fin d → ℝ) (ω : Tape)
    (s₀ : State) : ℝ :=
  match finalState P G ω s₀ with
  | some s => s.core.regs 0
  | none => 0

/-- The vector output of length `m`: real memory cells `0, …, m − 1` at the first halted state,
`0` if the run never halts. -/
noncomputable def outVec {n d : ℕ} (P : Program) (G : (Fin n → Fin d) → Fin d → ℝ) (ω : Tape)
    (s₀ : State) (m : ℕ) : Fin m → ℝ :=
  fun x => match finalState P G ω s₀ with
  | some s => s.core.mem (x : ℤ)
  | none => 0

/-- A deterministic oracle-free run: no query mapping (`n = d = 0`) and the all-zero tape. Used
for the projection subroutines (Fact 4.12, Lemma C.4, Proposition C.1), whose programs are
`OracleFree`, so neither is ever consulted. -/
noncomputable def detG : (Fin 0 → Fin 0) → Fin 0 → ℝ := fun _ _ => 0

/-- The all-zero tape. -/
def zeroTape : Tape := fun _ => 0

/-- The law of the tape: independent Uniform[0,1] cells. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

end DataDepProb.Discrete


