-- Prove2me | Definitions.Def_ClusterDecomp_Machine
-- name    : ClusterDecomp_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:48.388141+00:00
-- url     : https://prove2.me/theorems/4dc04691-6c86-48e6-bd2e-dd395577433e
-- title:
--   The randomized exact-arithmetic real RAM
-- statement:
--   A program is a finite list of instructions acting on real registers, integer pointers, real memory and integer memory indexed by $\mathbb Z$. The instructions are $+,-,\times,\div$ on reals (with $x/0=0$), rational literals, indirect load and store, pointer set, copy, increment, decrement, addition and subtraction, a comparison jump on reals and one on pointers, a cast from pointers to reals, a fair-coin instruction reading the next bit of a tape of independent fair coins, and `halt`. Each executed instruction costs one unit of work.
--
--   The paper's Theorem 1.1 says "there is a randomized algorithm that runs in $\widetilde O(\cdot)$ time" and names no machine; this model gives that sentence a meaning under which no computation is free.
--
--   **Formalization Note** The core is the published `SmaleNinth.RAMInstr`. There is no floor, real-to-integer cast, square root, power, exponential, logarithm, sort or pointer multiplication, and no constructor carries a function; `Admissible` makes literals rational and restricts the existentially chosen program, never the input. Reals are exact because the parameters $\varepsilon,p$ and the capacity $\beta\deg(v)$ are real. An invalid program counter is stuck and charged, so only `halt` halts, and a halted state stutters at no cost.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Theorem 1.1, p.2 (PDF p.4); the machine is a reading of this mission

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace ClusterDecomp

/-!
# The randomized exact-arithmetic real RAM

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…). Theorem 1.1 (p.2) says "there is a randomized algorithm that runs in Õ(·) time"
and the paper names no machine, so this model is a reading of the mission.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`. Its extensions are integer pointer
addition and subtraction, integer memory, a pointer-to-real cast, a fair-coin instruction and `halt`.

**Formalization Note.**
* Instructions are the core's `+ − × ÷` (with `x / 0 = 0`), literals, indirect real load and store, pointer set, copy,
  increment and decrement, the two comparison jumps; `pointerAdd`, `pointerSub`, `integerLoad`, `integerStore`,
  `pointerReal`; `coin`; `halt`.
* There is no floor, no real-to-integer cast, no sqrt, rpow, exp, log, sort or pointer multiplication, and no constructor
  carries a function. Real literals are rational (`Admissible`), and that restricts the existentially chosen program,
  never the input.
* Every executed instruction costs one unit of `work`, including `coin` and `halt`. An invalid program counter is stuck
  and charged, so only `halt` halts. After `halt` the state stutters at no cost.
* Randomness is a tape of independent fair coins, one bit per executed `coin`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]` on integer pointers.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`; the tape cursor advances.
* `halt`: stop; the output is read from memory. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | coin (dst : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input size. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions `accept`/`reject` do not occur (the machine stops
only through `halt`). -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P`: extension instructions are placeholders here and are always dispatched by `step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration (program counter, real registers, pointers, real memory), integer memory,
the coin-tape cursor, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  work : ℕ

/-- One step of program `P` on coin tape `ω`. Halted states stutter at no cost; every other step costs one unit of work.
`ω` occurs only in the `coin` branch. -/
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
    | some (.coin d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d (if ω s.cursor then 1 else 0) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀` on coin tape `ω`. -/
noncomputable def run (P : Program) (s₀ : State) (ω : ℕ → Bool) (t : ℕ) : State :=
  (step P ω)^[t] s₀

/-- The state at the start of a run: program counter, registers, pointers, cursor and work all `0`; integer memory holds
the list `ints` from cell `0`, real memory the list `reals` from cell `0`, and every other cell is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, false, 0⟩

/-- The output label of vertex `v` in a halted state: integer memory at `−1 − v`. -/
def label (s : State) (v : ℕ) : ℤ := s.integerMemory (-1 - (v : ℤ))

/-- The fair-coin tape: the product of uniform measures on `Bool` over `ℕ`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

end ClusterDecomp


