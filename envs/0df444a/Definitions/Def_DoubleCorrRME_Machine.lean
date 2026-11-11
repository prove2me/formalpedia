-- Prove2me | Definitions.Def_DoubleCorrRME_Machine
-- name    : DoubleCorrRME_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:09.098447+00:00
-- url     : https://prove2.me/theorems/49228109-74cd-40f5-b944-d672a21d6f64
-- title:
--   The coin-tape exact real RAM, its unit cost and its output
-- statement:
--   The paper's theorems assert that an algorithm exists with a stated running time but name no machine. This definition fixes one: a random-access machine over the reals whose program is one finite list of instructions.
--
--   The instructions are the published real pointer machine's $+,-,\times,\div$ (with $x/0=0$), rational literals, indirect load and store, pointer set, copy, increment, decrement and the two comparison jumps, together with integer pointer addition and subtraction, an integer memory, a pointer-to-real cast, $\sqrt{\cdot}$, a fair coin and `halt`. There is no floor, exp, log, power, Gaussian draw or sort. Every executed instruction costs one unit; an invalid program counter is stuck and charged, so only `halt` stops the machine. Randomness is a tape of independent fair coins, one per executed `coin`.
--
--   The output of a run is the vector stored in memory cells $-1,\dots,-d$ of the first halted state, and $0$ if the run never halts.
--
--   **Formalization Note** An `Admissible` program uses only rational literals and halts only through `halt`; this restricts the program that the theorems assert to exist, never the input. These are the weakest primitives the paper's method needs, which makes the existence statements as strong as possible.
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Theorem 1.3, p.2 (PDF p.3); Algorithms 2–7, pp.30–32, 62 (PDF pp.31–33, 63); machine is a reading of the mission (paper names none)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_DoubleCorrRME_Model

namespace DoubleCorrRME

/-!
# The randomized exact-arithmetic real RAM, its cost, and its output

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…). Theorem 1.3 (p.2) says
"there exists an algorithm (Algorithm 2) with running time Õ(Nnd)" and Theorem A.1 (p.63) bounds the
time of Algorithm 7; the paper names no machine, so this model is a reading of the mission.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`. Its extensions are
integer pointer addition and subtraction, integer memory, a pointer-to-real cast, `sqrt`, a fair-coin
instruction and `halt`.

**Formalization Note.**
* Instructions are the core's `+ − × ÷` (with `x / 0 = 0`), literals, indirect real load and store,
  pointer set, copy, increment and decrement, the two comparison jumps; `pointerAdd`, `pointerSub`,
  `integerLoad`, `integerStore`, `pointerReal`; `sqrt` (`Real.sqrt`: the thresholds `∆`, `ρ` of
  Algorithm 2, line 2, and the `√Λ` rescaling of Algorithm 7); `coin`; `halt`.
* There is no floor, no real-to-integer cast, no exp, log or power, no Gaussian draw, no argmin or
  sort, no pointer multiplication, and no constructor carries a function. Real literals are rational
  (`Admissible`), and that restricts the existentially chosen program, never the input.
* Every executed instruction costs one unit of `work`, including `coin` and `halt`. An invalid program
  counter is stuck and charged, so only `halt` halts. After `halt` the state stutters at no cost.
* Randomness is a tape of independent fair coins, one bit per executed `coin`.
* The output is the vector in memory cells `−1, …, −d` of the first halted state, and `0` if the run
  never halts.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor carries
a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]` on integer pointers.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `sqrt d a`: `r[d] := √(r[a])`.
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
noncomputable def outputVec (d : ℕ) (s : State) : Vec d :=
  WithLp.toLp 2 fun j => s.core.mem (-1 - (j : ℤ))

/-- The fair-coin tape: the product of uniform measures on `Bool` over `ℕ`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

open Classical in
/-- The output of the run of `P` from `s₀` on coin tape `ω`: the output vector of the first halted
state, and `0` if the run never halts. -/
noncomputable def output (P : Program) (d : ℕ) (s₀ : State) (ω : ℕ → Bool) : Vec d :=
  if h : ∃ t, (run P s₀ ω t).halted = true then outputVec d (run P s₀ ω (Nat.find h)) else 0

end DoubleCorrRME


