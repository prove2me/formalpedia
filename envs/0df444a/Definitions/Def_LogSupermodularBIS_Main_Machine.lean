-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Machine
-- name    : LogSupermodularBIS_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:30:58.386414+00:00
-- url     : https://prove2.me/theorems/dcfd5780-1bd1-4c28-8483-d9bead27238d
-- title:
--   The exact real-arithmetic model: costed randomized real RAM with a weight evaluator
-- statement:
--   This definition fixes the computational model of §2 (p. 9) and Appendix A (p. 38): exact real arithmetic in which arithmetic operations, comparisons, $\log$ and $\exp$ of reals, and an independent uniform draw from $(0,1)$ each cost one operation, every accessed graph entry or coefficient costs one operation, and each evaluation of the weight $W$ costs $T_W$ operations.
--
--   A **program** is a finite list of instructions of the published real RAM core `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$, literals, indirect real memory, integer pointer registers, comparison jumps), extended with integer addition and subtraction of pointers, an integer memory, a pointer-to-real cast, $\exp$, $\log$, a uniform draw `unif` that reads the next cell of a random tape $\omega\in\mathbb R^{\mathbb N}$, a weight evaluation `evalW` that reads a configuration $x\in\{0,1\}^d$ from $d$ consecutive integer cells and writes the exact value $W(x)$ into a real register, and `halt`. There is no floor or real-to-integer instruction: integer indices are obtained by comparisons. No instruction supplies a partition function, a conditional probability, an expectation or an optimization result. A program is **admissible** if all its literals are rational and it does not use the core's accept/reject; it is **oracle-free** if it never calls `evalW`.
--
--   Every executed instruction costs one operation, except `evalW`, which costs $T_W$. The **tape law** makes the tape cells independent and uniform on $(0,1)$; a tape is valid if all its cells lie in $(0,1)$. A run **halts within $T$** if it reaches `halt` with at most $T$ operations charged. The real output is real register $0$, and the configuration output of length $n$ is read from integer cells $0,\dots,n-1$ (it exists only if each holds $0$ or $1$), at the first halted state. The output law of a configuration $x$ is the tape probability of outputting $x$, and total variation is $\|\mu-\nu\|_{TV}=\tfrac12\sum_x|\mu(x)-\nu(x)|$.
--
--   **SamplesWithin** says that on every valid tape the run halts within $T$ and outputs a configuration, and that the output law is within total variation $\eta$ of the target. **CountsWithin** says that on every valid tape the run halts within $T$, and that with probability at least $1-\delta$ its real output $\widehat Z$ satisfies $|\widehat Z/Z-1|\le\epsilon$.
--
--   **Formalization Note.** Lean's total conventions give $\log 0=0$ and division by $0$ equal to $0$; an invalid program counter is stuck and charged, so only `halt` halts.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 9 (PDF 10), §2 model paragraph; p. 38 (PDF 39), Appendix A conventions; p. 3 (PDF 4), evaluator assumptions of Theorem 1.2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-!
# The exact real-arithmetic model of §2 (p. 9) and Appendix A (p. 38)

The published real-RAM core `SmaleNinth.RAMInstr` (exact `+ − × ÷`, literals, indirect real
memory, integer pointer registers with set/copy/increment/decrement, comparison jumps) is
extended with
* integer pointer addition/subtraction, an integer memory and a pointer-to-real cast;
* `exp` and `log` at unit cost (`Real.log`, so `log 0 = 0`; division by `0` is `0`);
* `unif dst`: `r[dst] :=` the next cell of a tape of independent Uniform(0,1) reals, unit cost;
* `evalW src dst`: reads a configuration `x ∈ {0,1}^d` from the integer memory cells
  `p[src], …, p[src]+d-1` and writes the exact value `W(x)` into `r[dst]`
  (`0` if some cell is not `0`/`1`); each call is charged `T_W` operations;
* `halt`.
There is no floor or real-to-integer instruction: integer indices are obtained by comparisons
(binary search), whose cost is charged step by step. No instruction carries a function, a
partition function, a conditional probability or an expectation: the weight is reachable only
through `evalW`. `Admissible` requires rational literals and forbids the core's accept/reject.
Every executed instruction costs one operation (`evalW` costs `T_W`); an invalid program counter
is stuck and charged, so only `halt` halts; a halted state stutters.
-/

/-- An exact weight evaluator: a dimension, a rational weight on `{0,1}^dim`, and the number
`cost = T_W` of operations charged per evaluation. -/
structure WeightOracle where
  dim : ℕ
  W : (Fin dim → Bool) → ℚ
  cost : ℕ

/-- The empty evaluator, used to run programs that never call `evalW`. -/
def noOracle : WeightOracle := ⟨0, fun _ => 1, 0⟩

/-- An instruction of the machine. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | unif (dst : ℕ)
  | evalW (src dst : ℕ)
  | halt

/-- A program: one finite list of instructions (a uniform algorithm). -/
abbrev Program := List Instr

/-- Every real literal is rational and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The program never calls the weight evaluator. -/
def OracleFree (P : Program) : Prop := ∀ op ∈ P, ∀ a b : ℕ, op ≠ .evalW a b

/-- The static core table of `P` (extension instructions are never executed by the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A random tape: one real per uniform draw. -/
abbrev Tape : Type := ℕ → ℝ

/-- The tapes in the uniform-draw domain: every cell lies in `(0,1)`. -/
def ValidTape (ω : Tape) : Prop := ∀ i, ω i ∈ Set.Ioo (0 : ℝ) 1

/-- The law of the tape: independent Uniform(0,1) cells. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)

/-- A machine state. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  work : ℕ

open Classical in
/-- The configuration stored in the integer memory cells `base, …, base+n-1`, if every cell
holds `0` or `1`. -/
noncomputable def readConfig (n : ℕ) (mem : ℤ → ℤ) (base : ℤ) : Option (Fin n → Bool) :=
  if ∀ i : Fin n, mem (base + i) = 0 ∨ mem (base + i) = 1 then
    some fun i => decide (mem (base + i) = 1)
  else none

/-- The value written by `evalW`: `W(x)` for a valid stored configuration, `0` otherwise. -/
noncomputable def oracleValue (O : WeightOracle) (c : Option (Fin O.dim → Bool)) : ℝ :=
  match c with
  | some x => (O.W x : ℝ)
  | none => 0

/-- One step of `P` with evaluator `O` and tape `ω`. -/
noncomputable def step (P : Program) (O : WeightOracle) (ω : Tape) (s : State) : State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
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
        { t with integerMemory :=
            Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal dst a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (s.core.ptrs a : ℝ) } }
    | some (.exp dst a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (Real.exp (s.core.regs a)) } }
    | some (.log dst a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (Real.log (s.core.regs a)) } }
    | some (.unif dst) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with regs := Function.update s.core.regs dst (ω s.cursor) } }
    | some (.evalW src dst) =>
        let val : ℝ := oracleValue O (readConfig O.dim s.integerMemory (s.core.ptrs src))
        { t with
          work := s.work + O.cost
          core := { t.core with regs := Function.update s.core.regs dst val } }
    | some .halt => { t with halted := true }

/-- The state after `k` steps. -/
noncomputable def run (P : Program) (O : WeightOracle) (ω : Tape) (s₀ : State) (k : ℕ) : State :=
  (step P O ω)^[k] s₀

/-- The initial state: pointer registers, integer memory and real memory hold the given lists
from index/cell `0`; everything else is `0`. -/
noncomputable def initState (ptrs : List ℤ) (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun i => ptrs.getD i 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, false, 0⟩

/-- The run halts with at most `T` operations charged (operations, uniform draws and `T_W` per
weight evaluation). -/
def HaltsWithin (P : Program) (O : WeightOracle) (ω : Tape) (s₀ : State) (T : ℝ) : Prop :=
  ∃ k : ℕ, (run P O ω s₀ k).halted = true ∧ ((run P O ω s₀ k).work : ℝ) ≤ T

open Classical in
/-- The first halted state of the run, if the run halts. -/
noncomputable def finalState (P : Program) (O : WeightOracle) (ω : Tape) (s₀ : State) :
    Option State :=
  if hk : ∃ k, (run P O ω s₀ k).halted = true then some (run P O ω s₀ (Nat.find hk)) else none

/-- The real output: real register `0` at the first halted state (`0` if the run never halts). -/
noncomputable def outReal (P : Program) (O : WeightOracle) (ω : Tape) (s₀ : State) : ℝ :=
  match finalState P O ω s₀ with
  | some s => s.core.regs 0
  | none => 0

/-- The configuration output: integer memory cells `0, …, n-1` at the first halted state, if the
run halts and every one of these cells holds `0` or `1`. -/
noncomputable def outConfig (P : Program) (O : WeightOracle) (ω : Tape) (s₀ : State) (n : ℕ) :
    Option (Fin n → Bool) :=
  match finalState P O ω s₀ with
  | some s => readConfig n s.integerMemory 0
  | none => none

/-- The probability that the output configuration is `x`. -/
noncomputable def outLaw (P : Program) (O : WeightOracle) (s₀ : State) (n : ℕ)
    (x : Fin n → Bool) : ℝ :=
  (tapeLaw {ω | outConfig P O ω s₀ n = some x}).toReal

/-- Total variation distance between two functions on a finite set: `½ Σ |p x − q x|`. -/
noncomputable def tvDist {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |p x - q x|

/-- A sampler run: on every tape in the uniform-draw domain the run halts within `T` operations
and outputs a configuration of length `n`; and the output law is within total variation `η` of
`target`. -/
def SamplesWithin (P : Program) (O : WeightOracle) (s₀ : State) (n : ℕ)
    (target : (Fin n → Bool) → ℝ) (η T : ℝ) : Prop :=
  (∀ ω, ValidTape ω → HaltsWithin P O ω s₀ T ∧ (outConfig P O ω s₀ n).isSome) ∧
  tvDist (outLaw P O s₀ n) target ≤ η

/-- A relative counter run: on every tape in the uniform-draw domain the run halts within `T`
operations, and with probability at least `1 - δ` its real output `Ẑ` satisfies
`|Ẑ / Z − 1| ≤ ε`. -/
def CountsWithin (P : Program) (O : WeightOracle) (s₀ : State) (Z ε δ T : ℝ) : Prop :=
  (∀ ω, ValidTape ω → HaltsWithin P O ω s₀ T) ∧
  ENNReal.ofReal (1 - δ) ≤ tapeLaw {ω | |outReal P O ω s₀ / Z - 1| ≤ ε}

end LogSupermodularBIS.Main


