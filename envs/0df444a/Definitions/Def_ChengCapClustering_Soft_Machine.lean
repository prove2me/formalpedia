-- Prove2me | Definitions.Def_ChengCapClustering_Soft_Machine
-- name    : ChengCapClustering_Soft_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:51:08.770413+00:00
-- url     : https://prove2.me/theorems/a9e42a25-6cd3-449b-ac77-15a0806ca2b6
-- title:
--   The deterministic arithmetic machine: unit-cost real RAM with integer pointers and real powers
-- statement:
--   The cost model of the paper (§2, printed p. 5: "arithmetic operations and evaluations of $\mathrm{dist}(x,y)^z$ count as single steps"; Lemma 5.5 also counts square roots and real powers). It extends the published real RAM `SmaleNinth.RAMInstr` (real registers and memory, $+,-,\times,\div$ with $x/0=0$, constants, indirect load/store through integer pointers, pointer set/copy/increment/decrement, comparison jumps) by:
--
--   - integer pointer addition and subtraction, an integer memory $\mathbb Z\to\mathbb Z$ with indirect load/store, and an integer-to-real cast;
--   - a real power `rpow`: $r_d := r_a^{\,r_b}$ when $r_a\ge 0$, and $0$ otherwise (so $x^{1/2}$ is the square root and $\mathrm{dist}^z$ one step);
--   - `halt`.
--
--   There is no floor, no real-to-integer cast, no integer multiplication and no randomness. A program is a finite instruction list; it is **admissible** if all its real literals are rational and it never uses the core's `accept`/`reject` (it stops only through `halt`). Irrational parameters such as $z,\varepsilon,\delta$ are passed as real input. Every executed instruction costs one step; a run that reaches an invalid program counter is stuck forever.
--
--   The input is two lists: integers in integer cells $0,1,\dots$ and reals in real cells $0,1,\dots$; all other cells are $0$. An output list is read from cells $-1,-2,\dots$ (entry $i$ at cell $-1-i$). `HaltsWithin P ints reals T Post` says that the run of $P$ on this input executes `halt` within $T$ steps and the halted state satisfies `Post`.
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), §2 (cost model), printed p. 5 / PDF p. 7; Lemma 5.5, printed p. 29 / PDF p. 31; Appendix C, printed p. 48 / PDF p. 50

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace ChengCapClustering.Soft

/-!
# The deterministic arithmetic machine (unit-cost real RAM with real powers)

Cheng, Mo, Ding, *Constant-Factor Approximation for Capacitated Clustering in Low Dimension with
(1 + ε)k Centers*, arXiv:2610.40625 (held manuscript SHA-256 9d298191…), §2, printed p. 5 / PDF p. 7:
"arithmetic operations and evaluations of dist(x, y)^z count as single steps"; Lemma 5.5 (printed
p. 29) also counts square roots and real powers as single steps.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (`+ − × ÷` with
`x / 0 = 0`, constants, indirect real load/store, pointer set/copy/increment/decrement, the two
comparison jumps). This module adds integer pointer addition and subtraction, an integer memory,
an integer-to-real cast, a real power and `halt`.

**Formalization Note.**
* `rpow d a b` sets `r[d] := r[a] ^ r[b]` (`Real.rpow`) when `r[a] ≥ 0` and `r[d] := 0` otherwise, so
  no trigonometric junk value of `Real.rpow` on negative bases is available. `x ^ (1/2)` is the
  square root.
* There is no floor, no real-to-integer cast, no integer multiplication and no randomness; no
  constructor carries a function. Real literals are rational (`Admissible`); irrational parameters
  (`z`, `ε`, `δ`, …) are passed to a program as part of its real input.
* Every executed instruction costs one unit of `work`, including `halt`. An invalid program counter
  is stuck and charged, so a run stops only through `halt`; after `halt` the state stutters.
* Inputs: integer memory cell `i ≥ 0` holds entry `i` of the integer input list, real memory cell
  `i ≥ 0` entry `i` of the real input list; every other cell is `0`. Outputs are read from the
  negative cells: entry `i` of an output list sits at cell `-1 - i`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]` on integer pointers.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `rpow d a b`: `r[d] := r[a] ^ r[b]` if `r[a] ≥ 0`, else `0`.
* `halt`: stop; the output is read from memory. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | rpow (dst base exponent : ℕ)
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
memory), the integer memory, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  intMem : ℤ → ℤ
  halted : Bool
  work : ℕ

/-- One step of program `P`. Halted states stutter at no cost; every other step costs one unit. -/
noncomputable def step (P : Program) (s : State) : State :=
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
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀`. -/
noncomputable def run (P : Program) (s₀ : State) (t : ℕ) : State :=
  (step P)^[t] s₀

/-- The state at the start of a run: program counter, registers, pointers and work all `0`; the
integer memory holds `ints` from cell `0`, the real memory holds `reals` from cell `0`, and every
other cell is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun c => if 0 ≤ c then reals.getD c.toNat 0 else 0⟩,
    fun c => if 0 ≤ c then ints.getD c.toNat 0 else 0, false, 0⟩

/-- The state `s` carries the output lists `ints` and `reals`: entry `i` of `ints` is in integer
cell `-1 - i` and entry `i` of `reals` is in real cell `-1 - i`. -/
def OutputIs (s : State) (ints : List ℤ) (reals : List ℝ) : Prop :=
  (∀ i : ℕ, i < ints.length → s.intMem (-1 - (i : ℤ)) = ints.getD i 0) ∧
    ∀ i : ℕ, i < reals.length → s.core.mem (-1 - (i : ℤ)) = reals.getD i 0

/-- Program `P`, started on the input lists `ints` and `reals`, executes `halt` within `T` steps,
and the halted state satisfies `Post`. -/
def HaltsWithin (P : Program) (ints : List ℤ) (reals : List ℝ) (T : ℝ) (Post : State → Prop) :
    Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ (run P (initState ints reals) t).halted = true ∧
    Post (run P (initState ints reals) t)

end ChengCapClustering.Soft


