-- Prove2me | Definitions.Def_PNormReg_Machine
-- name    : PNormReg_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:17.685948+00:00
-- url     : https://prove2.me/theorems/5ed06846-dd54-479a-a155-b752598df44d
-- title:
--   The randomized exact-arithmetic real RAM
-- statement:
--   The model of computation in which "there is an algorithm" is read. A program is one finite list of instructions, the same for every input size. The machine has real registers, integer pointers, a random-access real memory and an integer memory. Its instructions are:
--
--   1. exact $+,-,\times,\div$ (with $x/0=0$) on reals, rational literals, indirect real load and store;
--   2. pointer set, copy, increment, decrement, addition and subtraction, and integer load and store;
--   3. comparison jumps $r\le0$ and $p\le p'$, and a pointer-to-real cast;
--   4. $\sqrt{\cdot}$, the power $r_d:=|r_a|^{r_b}$, a fair coin, and halt.
--
--   There is no floor, no real-to-integer cast, no exponential, logarithm, argmin or sort, no pointer multiplication, and no instruction carries a function. Every executed instruction costs one unit of work. An invalid program counter is stuck and charged, and after halt the state stutters at no cost. The coin tape is a sequence of independent fair bits.
--
--   The machine makes "an algorithm" a finite syntactic object, so no running-time statement can compute its answer free of charge.
--
--   **Formalization Note** The core is the published `SmaleNinth.RAMInstr`. The paper names no machine; the choice is recorded in the mission's readings. Admissibility (rational literals, no core accept or reject) restricts the existentially chosen program, never the input. Floor is excluded because a real RAM with floor and unit-cost multiplication can pack many values in one cell.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), reading of Theorem 2, p.2; primitives motivated by pp.19, 25, 41

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace PNormReg

/-!
# The randomized exact-arithmetic real RAM

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…). The paper's theorems say "there is an algorithm"
(Theorem 2, p.2) and name no machine, so this model is a reading of the mission.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`. Its extensions are
integer pointer addition and subtraction, integer memory, a pointer-to-real cast, `sqrt`, `rpow`, a
fair-coin instruction and `halt`.

**Formalization Note.**
* Instructions are the core's `+ − × ÷` (with `x / 0 = 0`), literals, indirect real load and store,
  pointer set, copy, increment and decrement, the two comparison jumps; `pointerAdd`, `pointerSub`,
  `integerLoad`, `integerStore`, `pointerReal`; `sqrt` (`Real.sqrt`, used for Cholesky, p.25); `rpow`
  (`r[d] := |r[a]| ^ r[b]`, `Real.rpow`, so `0 ^ 0 = 1`, the paper's `|r_i|⁰ = 1`, p.19; the paper
  charges one step for these powers, p.41); `coin`; `halt`.
* There is no floor, no real-to-integer cast, no exp, log, argmin or sort, no pointer multiplication,
  and no constructor carries a function. Real literals are rational (`Admissible`), and that restricts
  the existentially chosen program, never the input.
* Every executed instruction costs one unit of `work`, including `coin` and `halt`. An invalid program
  counter is stuck and charged, so only `halt` halts. After `halt` the state stutters at no cost.
* Randomness is a tape of independent fair coins, one bit per executed `coin`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor carries
a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]` on integer pointers.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `sqrt d a`: `r[d] := √(r[a])`.
* `rpow d a b`: `r[d] := |r[a]| ^ r[b]`.
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`; the tape cursor advances.
* `halt`: stop; the output is read from memory. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | rpow (dst base exponent : ℕ)
  | coin (dst : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input size. -/
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

/-- A machine state: the core configuration (program counter, real registers, pointers, real memory),
integer memory, the coin-tape cursor, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  work : ℕ

/-- One step of program `P` on coin tape `ω`. Halted states stutter at no cost; every other step costs
one unit of work. `ω` occurs only in the `coin` branch. -/
noncomputable def step (P : Program) (ω : ℕ → Bool) (s : State) : State :=
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
    | some (.sqrt d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.sqrt (s.core.regs a)) } }
    | some (.rpow d a b) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (|s.core.regs a| ^ s.core.regs b) } }
    | some (.coin d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d (if ω s.cursor then 1 else 0) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀` on coin tape `ω`. -/
noncomputable def run (P : Program) (s₀ : State) (ω : ℕ → Bool) (t : ℕ) : State :=
  (step P ω)^[t] s₀

/-- The state at the start of a run: program counter, registers, pointers, cursor and work all `0`;
integer memory holds the list `ints` from cell `0`, real memory the list `reals` from cell `0`, and
every other cell is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, false, 0⟩

/-- The output vector of a halted run: `x̂_j := mem (−1 − j)` for `j < d`. -/
noncomputable def outputVec (d : ℕ) (s : State) : Fin d → ℝ :=
  fun j => s.core.mem (-1 - (j : ℤ))

/-- The fair-coin tape: the product of uniform measures on `Bool` over `ℕ`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

end PNormReg


