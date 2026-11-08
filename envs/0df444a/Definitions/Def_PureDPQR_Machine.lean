-- Prove2me | Definitions.Def_PureDPQR_Machine
-- name    : PureDPQR_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:48.291209+00:00
-- url     : https://prove2.me/theorems/b1bd1eb1-6942-4568-8bf3-41b5194e28f7
-- title:
--   The randomized exact real RAM of Remark 24 (uniform tape, exp, log, sqrt)
-- statement:
--   The cost model of Remark 24 (p.28): unit cost for exact real arithmetic $+,-,\times,\div$ and comparisons, for $\exp$, $\log$ and $\sqrt{\cdot}$, and for an independent Uniform$(0,1)$ draw. A **program** is a finite list of instructions of a unit-cost real RAM:
--
--   1. the published core `SmaleNinth.RAMInstr` (real arithmetic, rational literals, indirect real memory, pointer set/copy/increment/decrement, comparison jumps);
--   2. integer pointer addition and subtraction and an integer memory;
--   3. a pointer-to-real cast;
--   4. $\exp$, $\log$, $\sqrt{\cdot}$;
--   5. `unif`, which reads the next cell of a tape of independent Uniform$(0,1)$ values;
--   6. `halt`.
--
--   Every executed instruction costs one step. A program is **admissible** if its real literals are rational and it never uses the core's `accept`/`reject`. The **input** of Theorem 2 places $N,d,k,h_0,\dots,h_{d-1}$ in integer memory and $\varepsilon,\beta,N,d,k$, the table $q_i(j)$ (row-major, cell $5+id+j$) and $h_j$ (cell $5+kd+j$) in real memory; the output $\hat p_j$ is read from real cell $-1-j$ at the first halted state. The **law** of a program is the push-forward of the uniform tape under its output map.
--
--   **Formalization Note** There is no Laplace or Bernoulli instruction, no floor, no real-to-integer cast and no pointer multiplication: Laplace and Bernoulli draws are computed from uniforms ($-\mathrm{sgn}(U-\frac12)\log(1-2|U-\frac12|)/\kappa$ and $[U<\pi]$) at constant cost, so the machine is no stronger than the model of Remark 24. `log` is `Real.log` and division by $0$ is $0$. A non-measurable output map pushes forward to the zero measure, so a law equality with a probability measure forces measurability.
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Remark 24, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace PureDPQR

/-!
# The randomized exact real RAM of Remark 24, with a uniform tape

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…), Remark 24, p.28 (PDF p.29): "unit cost to each of the following:
arithmetic operations (addition, subtraction, multiplication, and division) and comparisons on real
numbers, performed without rounding error; exact evaluation of elementary functions such as
exponentials, logarithms, and square roots; and drawing an independent uniform random variable from
(0, 1). … We also assume unit-cost sampling from the Laplace distribution at any specified positive
rate."

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact `+ − × ÷`,
real literals, indirect real load and store, pointer set, copy, increment and decrement, and the two
comparison jumps). The extensions are integer pointer addition and subtraction, an integer memory, a
pointer-to-real cast, `exp`, `log`, `sqrt`, a uniform draw `unif`, and `halt`.

**Formalization Note.**
* `log` is `Real.log` (so `log 0 = 0`, `log x = log |x|`), `sqrt` is `Real.sqrt`, division by `0`
  gives `0` (the core's convention).
* There is no Laplace or Bernoulli instruction: a Laplace draw of rate `κ` is computed from one
  uniform `U` as `−sgn(U − 1/2) log(1 − 2|U − 1/2|)/κ`, and a Bernoulli(π) draw as `[U < π]`, at
  constant cost. So this machine is no stronger than the model of Remark 24.
* There is no floor, no real-to-integer cast, no pointer multiplication, and no constructor carries a
  function. Real literals of the chosen program are rational (`Admissible`); that restricts the
  existentially chosen program, never the input.
* Every executed instruction costs one unit of `work`, including `unif` and `halt`. An invalid
  program counter is stuck and charged, so only `halt` halts. After `halt` the state stutters at no
  cost.
* Randomness is a tape `ω : ℕ → ℝ` of independent Uniform(0,1) values (`uniformTape`), one value per
  executed `unif`.
* Input layout of Theorem 2 (`goalInput`): integer memory holds `N, d, k, h_0, …, h_{d−1}` from
  cell `0`; real memory holds `ε, β, N, d, k` in cells `0–4`, then the query table row-major
  (`q_i(j)` in cell `5 + i·d + j`), then `h_0, …, h_{d−1}` as reals (cell `5 + k·d + j`).
  Output: `p̂_j` is real memory cell `−1 − j`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor
carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]` on integer pointers.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `exp d a`, `log d a`, `sqrt d a`: `r[d] := exp r[a]`, `log r[a]`, `√r[a]`.
* `unif d`: `r[d] :=` the next value of the uniform tape; the tape cursor advances.
* `halt`: stop; the output is read from memory. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | sqrt (dst src : ℕ)
  | unif (dst : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions `accept`/`reject` do not
occur (the machine stops only through `halt`). -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P`: extension instructions are placeholders here and are always
dispatched by `step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration (program counter, real registers, pointers, real
memory), integer memory, the tape cursor, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  work : ℕ

/-- One step of program `P` on the uniform tape `ω`. Halted states stutter at no cost; every other
step costs one unit of work. `ω` occurs only in the `unif` branch. -/
noncomputable def step (P : Program) (ω : ℕ → ℝ) (s : State) : State :=
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
    | some (.sqrt d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.sqrt (s.core.regs a)) } }
    | some (.unif d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d (ω s.cursor) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀` on the tape `ω`. -/
noncomputable def run (P : Program) (s₀ : State) (ω : ℕ → ℝ) (t : ℕ) : State :=
  (step P ω)^[t] s₀

/-- The state at the start of a run: program counter, registers, pointers, cursor and work all `0`;
integer memory holds the list `ints` from cell `0`, real memory the list `reals` from cell `0`, and
every other cell is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, false, 0⟩

/-- The input of Theorem 2 (layout in the module note): integer memory `N, d, k, h_0, …, h_{d−1}`;
real memory `ε, β, N, d, k`, then `q_i(j)` in cell `5 + i·d + j`, then `h_j` in cell
`5 + k·d + j`. -/
noncomputable def goalInput (N d k : ℕ) (ε β : ℝ) (Q : Fin k → Fin d → ℝ) (h : Fin d → ℕ) :
    State :=
  initState ([(N : ℤ), (d : ℤ), (k : ℤ)] ++ List.ofFn fun j : Fin d => ((h j : ℕ) : ℤ))
    ([ε, β, (N : ℝ), (d : ℝ), (k : ℝ)] ++
      (List.ofFn fun m : Fin (k * d) =>
        Q (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) ++
      List.ofFn fun j : Fin d => ((h j : ℕ) : ℝ))

/-- The output vector of a state: `p̂_j := mem (−1 − j)` for `j < d`. -/
noncomputable def outputVec (d : ℕ) (s : State) : Fin d → ℝ :=
  fun j => s.core.mem (-1 - (j : ℤ))

open Classical in
/-- The output of the run of `P` from `s₀` on the tape `ω`: the output vector of the first halted
state, and `0` if the run never halts. -/
noncomputable def output (P : Program) (d : ℕ) (s₀ : State) (ω : ℕ → ℝ) : Fin d → ℝ :=
  if h : ∃ t, (run P s₀ ω t).halted = true then outputVec d (run P s₀ ω (Nat.find h)) else 0

/-- The law of one tape cell: the uniform distribution on `(0, 1)`. -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

instance : IsProbabilityMeasure unif01 := ⟨by simp [unif01]⟩

/-- The uniform tape: independent Uniform(0,1) values indexed by `ℕ`. -/
noncomputable def uniformTape : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => unif01

/-- The law of the output of `P` started in `s₀`: the push-forward of the uniform tape. (A
non-measurable output map pushes forward to the zero measure, so equating this law with a
probability measure forces measurability.) -/
noncomputable def programLaw (P : Program) (d : ℕ) (s₀ : State) : Measure (Fin d → ℝ) :=
  Measure.map (output P d s₀) uniformTape

/-- The run of `P` from `s₀` on the tape `ω` has halted by step `B`. -/
def HaltsWithin (P : Program) (s₀ : State) (B : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∃ t ≤ B, (run P s₀ ω t).halted = true

end PureDPQR


