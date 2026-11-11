-- Prove2me | Definitions.Def_LpSubspaceCoreset_SmallP_Machine
-- name    : LpSubspaceCoreset_SmallP_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:46:33.370857+00:00
-- url     : https://prove2.me/theorems/f3ed293b-58fd-440c-8ec6-725c615c8a7c
-- title:
--   The randomized unit-cost real RAM with real powers and a fair-coin tape
-- statement:
--   The paper states its running times for "a randomized algorithm" without naming a machine. The mission reads this as a **unit-cost randomized real RAM**: the published `SmaleNinth` real pointer machine (exact $+,-,\times,\div$ with $x/0=0$, constants, indirect real memory, pointers with set/copy/increment/decrement, comparison jumps), extended with integer pointer addition and subtraction, an integer memory, a pointer-to-real cast, a **guarded real power** ($r_a^{r_b}$ if $r_a\ge0$, else $0$; it gives square roots and the $p$-th powers that costs and Lewis weights need), a **fair-coin** instruction that reads the next bit of an infinite tape of independent fair coins, and `halt`.
--
--   Every executed instruction costs one unit; an invalid program counter is stuck and charged, so a run stops only through `halt`, after which the state is frozen. A program is a finite list of instructions, the same for every input, and is **admissible** when its real literals are rational and it never uses the core's accept/reject. The coin tape is distributed as the infinite product of fair Bernoulli measures.
--
--   **Formalization Note** There is no floor, real-to-integer cast, exp, log, sorting primitive or uniform real draw, and no instruction carries a function. Irrational parameters such as $p$ and $\varepsilon$ are passed as real inputs. The model combines the patterns of the published `ClusterDecomp_Machine` (coins) and `ChengCapClustering_Soft_Machine` (guarded power).
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), pp. 3–4 (Theorem 1.1, "randomized algorithm running in Õ_p(·) time"); reading of the mission

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace LpSubspaceCoreset.SmallP

/-!
# The randomized unit-cost real RAM with real powers

Lin, Mirrokni, Woodruff, arXiv:2608.26047, Theorem 1.1 (pp. 3–4) says "there is a randomized
algorithm running in Õ_p(·) time"; the paper names no machine, so this model is a reading of the
mission. It combines the patterns of the published `ClusterDecomp_Machine` (fair coins) and
`ChengCapClustering_Soft_Machine` (guarded real power), neither of which has both.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (`+ − × ÷` with
`x / 0 = 0`, constants, indirect real load and store, pointer set, copy, increment and decrement,
the two comparison jumps). The extensions are integer pointer addition and subtraction, an
integer memory, a pointer-to-real cast, a guarded real power, a fair-coin instruction and `halt`.

**Formalization Note.**
* `rpow d a b` sets `r[d] := r[a] ^ r[b]` (`Real.rpow`) when `r[a] ≥ 0` and `r[d] := 0`
  otherwise; `x ^ (1/2)` is the square root, and `x ^ p` the `p`-th powers that Lewis weights and
  ℓp costs need.
* There is no floor, no real-to-integer cast, no exp, log, sort, pointer multiplication or
  uniform real draw, and no constructor carries a function. Real literals are rational
  (`Admissible`); this restricts the existentially chosen program, never the input. Irrational
  parameters (`p`, `ε`, …) are passed as real inputs.
* Every executed instruction costs one unit of `work`, including `coin` and `halt`. An invalid
  program counter is stuck and charged, so only `halt` halts. After `halt` the state stutters at
  no cost.
* Randomness is an infinite tape of independent fair coins (`coinTape`), one bit per executed
  `coin`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor
carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]` on integer pointers.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `rpow d a b`: `r[d] := r[a] ^ r[b]` if `r[a] ≥ 0`, else `0`.
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`; the tape cursor advances.
* `halt`: stop; the output is read from memory. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | rpow (dst base exponent : ℕ)
  | coin (dst : ℕ)
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

/-- The guarded real power: `x ^ y` for `x ≥ 0`, and `0` for `x < 0`. -/
noncomputable def powStep (x y : ℝ) : ℝ := if 0 ≤ x then x ^ y else 0

/-- A machine state: the core configuration (program counter, real registers, pointers, real
memory), the integer memory, the coin-tape cursor, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  intMem : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  work : ℕ

/-- One step of program `P` on coin tape `ω`. Halted states stutter at no cost; every other step
costs one unit of work. `ω` occurs only in the `coin` branch. -/
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
            ptrs := Function.update s.core.ptrs d (s.intMem (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with intMem := Function.update s.intMem (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.rpow d a b) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (powStep (s.core.regs a) (s.core.regs b)) } }
    | some (.coin d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d (if ω s.cursor then 1 else 0) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀` on coin tape `ω`. -/
noncomputable def run (P : Program) (s₀ : State) (ω : ℕ → Bool) (t : ℕ) : State :=
  (step P ω)^[t] s₀

/-- The state at the start of a run: program counter, registers, pointers, cursor and work all
`0`; the integer memory holds the list `ints` from cell `0`, the real memory the list `reals`
from cell `0`, and every other cell is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, false, 0⟩

/-- The fair-coin tape: the product of uniform measures on `Bool` over `ℕ`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

end LpSubspaceCoreset.SmallP


