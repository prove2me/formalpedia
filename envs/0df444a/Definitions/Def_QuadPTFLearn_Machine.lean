-- Prove2me | Definitions.Def_QuadPTFLearn_Machine
-- name    : QuadPTFLearn_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:21:51.54648+00:00
-- url     : https://prove2.me/theorems/af535cc3-927f-4dc5-ae1a-2764f0b81469
-- title:
--   The deterministic arithmetic sampling real RAM (exact field arithmetic, comparisons, pointers, sample, halt)
-- statement:
--   The model of computation in which the algorithmic statements of the mission are posed.
--
--   A program is a finite list of instructions. The machine has real registers, integer pointer registers and a random-access memory indexed by integers. Its instructions are the published real-RAM core (exact addition, subtraction, multiplication and division, rational literals, indirect load and store through pointers, pointer set, copy, increment and decrement, and the comparison jumps $r\le0$ and $p\le p'$), together with:
--
--   1. a cast of a pointer register to a real register;
--   2. `sample q`, which writes the next unread sample $X\in\mathbb R^n$ of an i.i.d. stream to the memory cells $p[q],\dots,p[q]+n-1$;
--   3. `halt`.
--
--   There is no square root, exponential, logarithm, floor and no source of random bits; the sample stream is the only randomness. Every executed instruction costs one unit of work, except `sample`, which costs $n$. A run starts with $n$ in pointer register $0$ and the input list in memory from cell $0$. A run **halts within** $B_s,B_w$ if on every sample stream it reaches `halt` after at most $B_s$ samples and $B_w$ work; it **succeeds with probability** $p$ if a measurable set of streams of probability at least $p$ makes every halted state satisfy the success condition.
--
--   The machine counts the "arithmetic operations" that the paper's complexity analyses count.
--
--   **Formalization Note** The program is required to use rational literals only and to stop only through `halt`. An invalid program counter is a stuck state that is charged work, and after `halt` the state does not change. In the learning statements $n=d+1$: the point and then its label.
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 1.3 ("samples and time"), p.2 (PDF p.4); proof of Theorem 8.1, p.81 (PDF p.83) and of Theorem 9.1, pp.92–93 (PDF pp.94–95): "arithmetic operations"

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace QuadPTFLearn

/-!
# The deterministic arithmetic sampling real RAM

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 1.3, p.2 (PDF p.4) says "There is an algorithm … using … samples and time"; the proofs
of Theorem 8.1 (p.81, PDF p.83) and Theorem 9.1 (pp.92–93, PDF pp.94–95) count "arithmetic
operations". The paper fixes no instruction list, so this machine is a reading of those words.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact
`+ − × ÷`, literals, indirect load and store through integer pointers, pointer set, copy,
increment and decrement, and the comparison jumps `r ≤ 0` and `p ≤ p'`). The extensions are a
pointer-to-real cast, a `sample` instruction and `halt`.

**Formalization Note.**
* There is no square root, exponential, logarithm, trigonometric function, floor, real-to-integer
  cast and no coin: the only randomness is the sample stream. Every real literal is rational and
  the core `accept`/`reject` do not occur (`Admissible`); this restricts the existentially chosen
  program, never the input.
* `sample q` writes the coordinates of the next unread sample `X ∈ ℝⁿ` to memory cells
  `p[q], p[q] + 1, …, p[q] + n − 1`. It is the only access the program has to the unknown
  distribution. In the learning statements `n = d + 1`: the point and then its label.
* Cost: every executed instruction adds `1` to `work`, except `sample`, which adds `n` (writing
  `n` coordinates). An invalid program counter is stuck and charged, so only `halt` halts. After
  `halt` the state stutters at no cost. `samplesUsed` counts the executed `sample` instructions.
* The machine is the template `GaussMixHH.Machine` (41014cbf) without its `sqrt`, `exp`, `cos`,
  `sin` and `coin` instructions and without the coin tape.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor
carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerReal d q`: `r[d] := (p[q] : ℝ)`.
* `sample q`: `M[p[q] + i] := X_k i` for `i < n`, where `X_k` is the next unread sample.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerReal (dst pointer : ℕ)
  | sample (pointer : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every dimension and every input. -/
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

/-- A machine state: the core configuration (program counter, real registers, pointers, memory),
the number of samples read so far, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  samplesUsed : ℕ
  halted : Bool
  work : ℕ

/-- Write the sample `x ∈ ℝⁿ` to the memory cells `base, …, base + n − 1`. -/
noncomputable def writeSample {n : ℕ} (mem : ℤ → ℝ) (base : ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    ℤ → ℝ :=
  fun a => if h : base ≤ a ∧ a - base < n then
      x ⟨(a - base).toNat, by omega⟩
    else mem a

/-- One step of program `P` in dimension `n` on the sample stream `xs`. Halted states stutter at
no cost; `sample` costs `n`, every other step costs `1`. -/
noncomputable def step (P : Program) (n : ℕ) (xs : ℕ → EuclideanSpace ℝ (Fin n)) (s : State) :
    State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerReal d q) =>
        { t with core := { t.core with regs := Function.update s.core.regs d (s.core.ptrs q : ℝ) } }
    | some (.sample q) =>
        { t with
          work := s.work + n
          samplesUsed := s.samplesUsed + 1
          core := { t.core with mem := writeSample s.core.mem (s.core.ptrs q) (xs s.samplesUsed) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` in dimension `n` from `s₀`, on the sample stream `xs`. -/
noncomputable def run (P : Program) (n : ℕ) (s₀ : State) (xs : ℕ → EuclideanSpace ℝ (Fin n))
    (t : ℕ) : State :=
  (step P n xs)^[t] s₀

/-- The state at the start of a run: program counter, registers, counters and work `0`; pointer
register `0` holds `n` and all other pointers are `0`; memory holds the list `reals` from cell `0`,
and every other cell is `0`. -/
noncomputable def initState (n : ℕ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun q => if q = 0 then (n : ℤ) else 0,
      fun a => if 0 ≤ a then reals.getD a.toNat 0 else 0⟩, 0, false, 0⟩

/-- On every sample stream the run halts, having read at most `Bs` samples and done at most `Bw`
work. -/
def HaltsWithin (P : Program) (n : ℕ) (s₀ : State) (Bs Bw : ℝ) : Prop :=
  ∀ xs : ℕ → EuclideanSpace ℝ (Fin n), ∃ t : ℕ, (run P n s₀ xs t).halted = true ∧
    ((run P n s₀ xs t).samplesUsed : ℝ) ≤ Bs ∧ ((run P n s₀ xs t).work : ℝ) ≤ Bw

/-- With probability at least `prob` under the stream law `μ`, every halted state of the run
satisfies `Good`: there is a measurable event `E` with `prob ≤ μ E` on which this holds. -/
def SucceedsWP (P : Program) (n : ℕ) (s₀ : State) (μ : Measure (ℕ → EuclideanSpace ℝ (Fin n)))
    (prob : ENNReal) (Good : State → Prop) : Prop :=
  ∃ E : Set (ℕ → EuclideanSpace ℝ (Fin n)), MeasurableSet E ∧ prob ≤ μ E ∧
    ∀ xs ∈ E, ∀ t : ℕ, (run P n s₀ xs t).halted = true → Good (run P n s₀ xs t)

/-- The output region of a halted state: its memory and the base address `p[1]`. -/
def outMem (s : State) : ℤ → ℝ := s.core.mem

/-- The output base address `p[1]`. -/
def outBase (s : State) : ℤ := s.core.ptrs 1

end QuadPTFLearn


