-- Prove2me | Definitions.Def_SoSPlantedCSP_Reduction_Machine
-- name    : SoSPlantedCSP_Reduction_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:16.126451+00:00
-- url     : https://prove2.me/theorems/f5f6e48c-2b50-4283-88e6-891af5695f5d
-- title:
--   The randomized unit-cost real RAM (real pointer machine plus a uniform tape)
-- statement:
--   The algorithms of the mission are programs of a **randomized real RAM**. Its deterministic core is the published real pointer machine `SmaleNinth.RAMInstr`: real registers, integer pointer registers, a real memory $M:\mathbb Z\to\mathbb R$ addressed through pointers, real constants, exact $+,-,\times,\div$, pointer set/copy/increment/decrement, the jumps "if $r\le 0$" and "if $p\le p'$", and `accept`/`reject`. There is no floor, no real-to-integer conversion and no bit extraction.
--
--   The only extension is the instruction $\mathrm{unif}\ d$, which writes the next unread coordinate of the **random tape** into register $d$. The tape is a sequence $\omega=(\omega_0,\omega_1,\dots)\in[0,1]^{\mathbb N}$ of independent uniform numbers on $[0,1]$; its law is the product measure $\mathbb P_{\mathrm{tape}}$.
--
--   A run on input memory $x$ starts with program counter $0$, all registers and pointers $0$, and memory $x$. Each step executes one instruction. A state whose program counter is outside the program or carries `accept` or `reject` is **halted**, and a step leaves it unchanged. The program **halts within $T$ steps** on $(x,\omega)$ if the state after some $t\le T$ steps is halted; the **output** is the memory of the first halted state.
--
--   This is the cost model of every running-time claim of the mission: running time is the number of executed instructions.
--
--   **Formalization Note** Lean's $x/0=0$ is harmless because a program can test a divisor first. The tape coordinates are elements of `unitInterval` with Lebesgue measure.
-- source:
--   Arpon Basu, Andrew D. Lin, Peter Manohar, STOC 2027 submission #544 (October 2026), machine model of Theorem 3.1 and Lemmas 3.5, 3.6, pp. 10–11 (PDF pp. 12–13); the paper names no model, the core is the published SmaleNinth_RealRAM

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace SoSPlantedCSP.Reduction

/-!
# The randomized unit-cost real RAM

Basu–Lin–Manohar, *Sum-of-Squares Refutation Implies Planted Recovery for Semirandom CSPs*,
STOC 2027 submission #544 (October 2026): Theorem 3.1 and Lemmas 3.5, 3.6 (printed pp. 10–11,
PDF pp. 12–13) speak of "an algorithm that … in time T outputs …" and of "randomized"
algorithms; the paper fixes no machine model. This module fixes one.

* The deterministic core is the published real pointer machine `SmaleNinth.RAMInstr`
  (real constants, `+ − × ÷` with Lean's `x / 0 = 0`, indirect load/store through integer
  pointers, pointer set/copy/increment/decrement, the jumps `r ≤ 0` and `p ≤ p'`, `accept`,
  `reject`). There is no floor, no real-to-integer conversion and no bit extraction.
* The only extension is `unif d`: `r[d] :=` the next unread coordinate of the random tape.
* The random tape is a sequence of independent uniform `[0,1]` numbers (`tapeLaw`).
* Every executed instruction costs one step. A configuration whose program counter carries
  `accept` or `reject`, or lies outside the program, is halted and is not changed by a step.
-/

/-- An instruction: a core real-RAM instruction, or a uniform draw from the tape. -/
inductive Instr : Type
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] :=` the next unread coordinate of the random tape. -/
  | unif (dst : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- The random tape: an infinite sequence of numbers in `[0,1]`. -/
abbrev Tape := ℕ → unitInterval

/-- The core instruction table of a program (a `unif` is replaced by a placeholder that `step`
never executes through the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | .unif _ => .const 0 0

/-- A machine state: the core configuration (program counter, real registers, pointer
registers, memory `ℤ → ℝ`) and the position of the next unread tape coordinate. -/
structure State where
  /-- Program counter, registers, pointers, memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- Next unread coordinate of the tape. -/
  cursor : ℕ

/-- The state `s` is halted under `P`: its program counter is outside `P` or carries
`accept` or `reject`. -/
def Halted (P : Program) (s : State) : Prop :=
  P[s.cfg.pc]? = none ∨ P[s.cfg.pc]? = some (.core .accept) ∨
    P[s.cfg.pc]? = some (.core .reject)

/-- One step of `P` on the tape `ω`. A halted state is unchanged. -/
noncomputable def step (P : Program) (ω : Tape) (s : State) : State :=
  match P[s.cfg.pc]? with
  | none => s
  | some (.core _) => ⟨SmaleNinth.RAMStep (coreProgram P) s.cfg, s.cursor⟩
  | some (.unif d) =>
      ⟨⟨s.cfg.pc + 1, Function.update s.cfg.regs d (ω s.cursor : ℝ), s.cfg.ptrs, s.cfg.mem⟩,
        s.cursor + 1⟩

/-- The start state on input memory `x`: program counter `0`, all registers and pointers `0`,
memory `x`, nothing read from the tape. -/
def initState (x : ℤ → ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, x⟩, 0⟩

/-- The state after `t` steps of `P` on input memory `x` and tape `ω`. -/
noncomputable def run (P : Program) (x : ℤ → ℝ) (ω : Tape) (t : ℕ) : State :=
  (step P ω)^[t] (initState x)

/-- `P`, run on input memory `x` and tape `ω`, is halted after at most `T` steps. -/
def HaltsWithin (P : Program) (x : ℤ → ℝ) (ω : Tape) (T : ℕ) : Prop :=
  ∃ t ≤ T, Halted P (run P x ω t)

open Classical in
/-- The memory of the halted state of the run (the output). For a run that never halts this
is the input memory; it is only used on runs that halt. -/
noncomputable def finalMem (P : Program) (x : ℤ → ℝ) (ω : Tape) : ℤ → ℝ :=
  if h : ∃ t, Halted P (run P x ω t) then (run P x ω (Nat.find h)).cfg.mem else x

/-- The law of the tape: independent coordinates, each uniform on `[0,1]`. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

instance : IsProbabilityMeasure tapeLaw := by
  unfold tapeLaw; infer_instance

end SoSPlantedCSP.Reduction


