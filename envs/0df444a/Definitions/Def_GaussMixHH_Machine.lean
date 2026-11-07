-- Prove2me | Definitions.Def_GaussMixHH_Machine
-- name    : GaussMixHH_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:56.32773+00:00
-- url     : https://prove2.me/theorems/41014cbf-a8a3-4f78-8325-dda098948e7c
-- title:
--   The randomized sampling real RAM (the real arithmetic model)
-- statement:
--   The model of computation in which "there is an algorithm" (Theorems 1 and 20) is read. The paper says only that "all running times are measured in the real arithmetic model" (§3, p.15).
--
--   A program is one finite list of instructions, the same for every dimension $n$ and every input. The machine has real registers $r_0,r_1,\dots$, integer pointer registers $p_0,p_1,\dots$ and a random-access real memory indexed by $\mathbb Z$. Its instructions are:
--
--   1. exact $+,-,\times,\div$ on reals (with $x/0=0$), rational literals, indirect load and store through pointers, pointer set, copy, increment and decrement, and the comparison jumps $r_i\le0$ and $p_q\le p_{q'}$ (the published real-RAM core);
--   2. a pointer-to-real cast $r_d:=p_q$;
--   3. $\sqrt{\cdot}$, $\exp$, $\cos$ and $\sin$ of a register;
--   4. a fair coin $r_d\in\{0,1\}$;
--   5. $\mathrm{sample}\ q$, which writes the coordinates of the next unread sample $X_k\in\mathbb R^n$ into the memory cells $p_q,\dots,p_q+n-1$;
--   6. halt; the output is $r_0$.
--
--   There is no floor, real-to-integer cast, logarithm, real power or uniform-real draw, and no instruction carries a function. Every executed instruction costs one unit of work except $\mathrm{sample}$, which costs $n$. An invalid program counter is stuck and charged, and after halt the state stutters at no cost. The number of executed $\mathrm{sample}$ instructions is the sample count.
--
--   The model is weak enough that the unknown distribution is reachable only through $\mathrm{sample}$, and strong enough for the paper's algorithm: $e^{i\theta\|X-z\|^2}$ and the kernels $K_u(\theta)$ are computed with $\exp$, $\cos$, $\sin$ at unit cost, as in the paper's runtime count (p.28).
--
--   **Formalization Note** The core is the published `SmaleNinth.RAMInstr`; `Admissible` requires rational literals and excludes the core `accept`/`reject`, restricting the existentially chosen program only. Coins are read from an infinite tape, one bit per `coin`; samples from a separate stream, the $k$-th executed `sample` reading entry $k$.
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), §3, p.15 (PDF p.17) "real arithmetic model"; Theorems 1 and 20, pp.4, 25; runtime count, p.28

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace GaussMixHH

/-!
# The randomized sampling real RAM

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…). Theorems 1 and 20 (pp.4, 25) say
"there is an algorithm", and §3, p.15, says "All running times are measured in the real arithmetic
model." No instruction list is given, so this machine is a reading of that sentence.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact `+ − × ÷`,
literals, indirect load and store through integer pointers, pointer set, copy, increment and
decrement, and the comparison jumps `r ≤ 0` and `p ≤ p'`). The extensions are a pointer-to-real
cast, `√`, `exp`, `cos`, `sin`, a fair coin, a `sample` instruction and `halt`.

**Formalization Note.**
* Real literals are rational and the core `accept`/`reject` do not occur (`Admissible`). This
  restricts the existentially chosen program, never the input. No constructor carries a function,
  and there is no floor, real-to-integer cast, logarithm, real power or uniform-real draw.
* `sample q` writes the coordinates of the next unread sample `X_k ∈ ℝⁿ` to memory cells
  `p[q], p[q] + 1, …, p[q] + n − 1`. It is the only access the program has to the unknown
  distribution.
* Cost: every executed instruction adds `1` to `work`, except `sample`, which adds `n` (writing
  `n` coordinates). An invalid program counter is stuck and charged, so only `halt` halts. After
  `halt` the state stutters at no cost. `samplesUsed` counts the executed `sample` instructions.
* Randomness is a tape of independent fair bits, one bit per executed `coin`; the samples come
  from a separate stream, the `k`-th executed `sample` reading entry `k`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor
carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerReal d q`: `r[d] := (p[q] : ℝ)`.
* `sqrt d a`, `exp d a`, `cos d a`, `sin d a`: `r[d] := √r[a]`, `e^{r[a]}`, `cos r[a]`, `sin r[a]`
  (`Real.sqrt`, so `√x = 0` for `x < 0`).
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`.
* `sample q`: `M[p[q] + i] := X_k i` for `i < n`, where `X_k` is the next unread sample.
* `halt`: stop; the output is register `r[0]`. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | cos (dst src : ℕ)
  | sin (dst src : ℕ)
  | coin (dst : ℕ)
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
the coin-tape cursor, the number of samples read so far, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  coinCursor : ℕ
  samplesUsed : ℕ
  halted : Bool
  work : ℕ

/-- Write the sample `x ∈ ℝⁿ` to the memory cells `base, …, base + n − 1`. -/
noncomputable def writeSample {n : ℕ} (mem : ℤ → ℝ) (base : ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    ℤ → ℝ :=
  fun a => if h : base ≤ a ∧ a - base < n then
      x ⟨(a - base).toNat, by omega⟩
    else mem a

/-- One step of program `P` in dimension `n`, on coin tape `coins` and sample stream `xs`.
Halted states stutter at no cost; `sample` costs `n`, every other step costs `1`. -/
noncomputable def step (P : Program) (n : ℕ) (coins : ℕ → Bool)
    (xs : ℕ → EuclideanSpace ℝ (Fin n)) (s : State) : State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    let setReg (d : ℕ) (v : ℝ) : State :=
      { t with core := { t.core with regs := Function.update s.core.regs d v } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerReal d q) => setReg d (s.core.ptrs q : ℝ)
    | some (.sqrt d a) => setReg d (Real.sqrt (s.core.regs a))
    | some (.exp d a) => setReg d (Real.exp (s.core.regs a))
    | some (.cos d a) => setReg d (Real.cos (s.core.regs a))
    | some (.sin d a) => setReg d (Real.sin (s.core.regs a))
    | some (.coin d) =>
        { setReg d (if coins s.coinCursor then 1 else 0) with coinCursor := s.coinCursor + 1 }
    | some (.sample q) =>
        { t with
          work := s.work + n
          samplesUsed := s.samplesUsed + 1
          core := { t.core with mem := writeSample s.core.mem (s.core.ptrs q) (xs s.samplesUsed) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` in dimension `n` from `s₀`, on the randomness
`ω = (coin tape, sample stream)`. -/
noncomputable def run (P : Program) (n : ℕ) (s₀ : State)
    (ω : (ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin n))) (t : ℕ) : State :=
  (step P n ω.1 ω.2)^[t] s₀

/-- The state at the start of a run: program counter, registers, cursors and work `0`; pointer
register `0` holds `n` and all other pointers are `0`; memory holds the list `reals` from cell `0`,
and every other cell is `0`. -/
noncomputable def initState (n : ℕ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun q => if q = 0 then (n : ℤ) else 0,
      fun a => if 0 ≤ a then reals.getD a.toNat 0 else 0⟩, 0, 0, false, 0⟩

/-- The output of a run: register `r[0]`. -/
def output (s : State) : ℝ := s.core.regs 0

/-- The fair-coin tape: the product of uniform measures on `Bool` over `ℕ`. -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

end GaussMixHH


