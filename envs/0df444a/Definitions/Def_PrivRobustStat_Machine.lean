-- Prove2me | Definitions.Def_PrivRobustStat_Machine
-- name    : PrivRobustStat_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:16.109786+00:00
-- url     : https://prove2.me/theorems/136eea66-ff32-468f-8f13-6866e0fa50d1
-- title:
--   The randomized real RAM with a Gaussian tape, its cost, and the input layout of Theorem 4
-- statement:
--   Theorem 4 says "there is an algorithm" running in a stated time, and the paper names no machine. The mission fixes one: a finite program over a pointer RAM with exact real arithmetic, built on the published `SmaleNinth.RAMInstr` core. Its instructions are rational literals, $+,-,\times,\div$ (with $x/0=0$), indirect loads and stores, integer pointers with $+,-$, integer memory, the cast of a pointer to a real, $\lfloor\cdot\rfloor$ from a real into a pointer, $\sqrt{\cdot}$, $|a|^b$, $\log$, a draw `gauss` that reads the next value of a tape of independent $\mathcal N(0,1)$ reals, and `halt`. Every executed instruction costs one unit of work; after `halt` the state no longer changes.
--
--   The input of Theorem 4 is placed with $d,n$ in integer memory and $\alpha,\beta,\varepsilon,\delta$ followed by the $nd$ coordinates of $x_1,\dots,x_n$ in real memory; the estimate $\hat\mu\in\mathbb R^d$ is read from cells $-1,\dots,-d$ of the first halted state.
--
--   **Formalization Note** No instruction carries a function, and there is no exp, sort or argmin. Laplace noise $\mathrm{Lap}(b)$ is exactly $b(g_1^2+g_2^2-g_3^2-g_4^2)/2$ from four Gaussian draws. The floor instruction is kept because Algorithm 6 bins unbounded real data; a real RAM with floor and unit-cost multiplication can pack several numbers into one cell, so its step count may understate bit work.
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Theorem 4, p.33 (the machine and layout are a reading: the paper names none)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-!
# The randomized exact-arithmetic real RAM with a Gaussian tape

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…). Theorem 4 (p.33, PDF p.36) says "There is an algorithm …
The algorithm runs in time O(nd log³(d) log²(nd/(αβ)))" and names no machine, so this model is a
reading of the mission.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`. The extensions are
integer pointer addition and subtraction, integer memory, a pointer-to-real cast, `floor`, `sqrt`,
`rpow`, `log`, a standard Gaussian draw `gauss`, and `halt`.

**Formalization Note.**
* Instructions: the core's `+ − × ÷` (with `x / 0 = 0`), literals, indirect real load and store,
  pointer set, copy, increment and decrement, the two comparison jumps; `pointerAdd`, `pointerSub`,
  `integerLoad`, `integerStore`, `pointerReal`; `floor` (`p[d] := ⌊r[a]⌋`, used for the bins
  `I_k = [16k, 16(k+1))` of Algorithm 6, p.31); `sqrt` (`Real.sqrt`); `rpow`
  (`r[d] := |r[a]| ^ r[b]`); `log` (`Real.log`, so `log 0 = 0` and `log x = log |x|`); `gauss`; `halt`.
* There is no exp, sort, argmin, real-to-real floor or pointer multiplication, and no constructor
  carries a function. Real literals are rational (`Admissible`); that restricts the existentially
  chosen program, never the input.
* Every executed instruction costs one unit of `work`, including `gauss` and `halt`. An invalid
  program counter is stuck and charged, so only `halt` halts. After `halt` the state stutters at no
  cost.
* Randomness is a tape `ω : ℕ → ℝ` of independent standard Gaussians (`gaussTape`), one value per
  executed `gauss`. The paper's Gaussian mechanism (Algorithms 2, 3, 4, 7) needs exact Gaussians;
  Laplace noise `Lap(b)` of Algorithm 6 is exactly `b·(g₁² + g₂² − g₃² − g₄²)/2` from four draws.
* Known weakness: a real RAM with `floor` and unit-cost multiplication can pack several numbers into
  one cell (Schönhage 1979), so its step count can understate bit work. `floor` is kept because the
  paper's Algorithm 6 bins unbounded real data and Lemma 13 charges `O(nd log n)` for it.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor carries
a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]` on integer pointers.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `floor d a`: `p[d] := ⌊r[a]⌋`.
* `sqrt d a`: `r[d] := √(r[a])`.
* `rpow d a b`: `r[d] := |r[a]| ^ r[b]`.
* `log d a`: `r[d] := log (r[a])`.
* `gauss d`: `r[d] :=` the next value of the Gaussian tape; the tape cursor advances.
* `halt`: stop; the output is read from memory. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | floor (dst src : ℕ)
  | sqrt (dst src : ℕ)
  | rpow (dst base exponent : ℕ)
  | log (dst src : ℕ)
  | gauss (dst : ℕ)
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
integer memory, the Gaussian-tape cursor, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  work : ℕ

/-- One step of program `P` on Gaussian tape `ω`. Halted states stutter at no cost; every other step
costs one unit of work. `ω` occurs only in the `gauss` branch. -/
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
        { t with integerMemory := Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.floor d a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d ⌊s.core.regs a⌋ } }
    | some (.sqrt d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.sqrt (s.core.regs a)) } }
    | some (.rpow d a b) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (|s.core.regs a| ^ s.core.regs b) } }
    | some (.log d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.log (s.core.regs a)) } }
    | some (.gauss d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d (ω s.cursor) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀` on Gaussian tape `ω`. -/
noncomputable def run (P : Program) (s₀ : State) (ω : ℕ → ℝ) (t : ℕ) : State :=
  (step P ω)^[t] s₀

/-- The state at the start of a run: program counter, registers, pointers, cursor and work all `0`;
integer memory holds the list `ints` from cell `0`, real memory the list `reals` from cell `0`, and
every other cell is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, false, 0⟩

/-- The output vector of a state: `µ̂_j := mem (−1 − j)` for `j < d`, as a Euclidean vector. -/
noncomputable def outputVec (d : ℕ) (s : State) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun j => s.core.mem (-1 - (j : ℤ))

/-- The Gaussian tape: independent standard Gaussians `N(0, 1)` indexed by `ℕ`. -/
noncomputable def gaussTape : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- The input of Theorem 4. Integer memory: cell `0` is `d`, cell `1` is `n`. Real memory:
`α, β, ε, δ` in cells `0, 1, 2, 3`, then the data points `x₁, …, x_n`, each as its `d` coordinates in
order, so coordinate `a` of `x_i` (0-based `i`, `a`) is in cell `4 + i·d + a`. -/
noncomputable def goalInput (d n : ℕ) (α β ε δ : ℝ) (X : Fin n → EuclideanSpace ℝ (Fin d)) :
    State :=
  initState [(d : ℤ), (n : ℤ)]
    ([α, β, ε, δ] ++ List.ofFn fun k : Fin (n * d) =>
      X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

open Classical in
/-- The output of the run of `P` from `s₀` on tape `ω`: the output vector of the first halted state,
and `0` if the run never halts. -/
noncomputable def output (P : Program) (d : ℕ) (s₀ : State) (ω : ℕ → ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  if h : ∃ t, (run P s₀ ω t).halted = true then outputVec d (run P s₀ ω (Nat.find h)) else 0

end PrivRobustStat


