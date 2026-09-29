-- Prove2me | Definitions.Def_SmaleNinth_RealRAM
-- name    : SmaleNinth_RealRAM
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-07T18:40:20.552017+00:00
-- url     : https://prove2.me/theorems/40a13078-ae7f-403e-b30b-476243e24e78
-- title:
--   Pointer machines over $\mathbb{R}$ (real RAM)
-- statement:
--   A **pointer machine over the real numbers** is the random-access counterpart of the tape machine of the mission. It has finitely many real registers $r_0, r_1, \dots$ (as many as the program mentions), finitely many integer pointer registers $p_0, p_1, \dots$, and a memory $M : \mathbb{Z} \to \mathbb{R}$ which initially holds the input in the same layout as the tape of the tape machine.
--
--   **Instructions.** Real registers support loading a real constant and exact field arithmetic $+, -, \times, \div$ (with $x/0 = 0$, the same benign totalisation as in the tape model). Memory is accessed only through pointers: `load dst q` sets $r_{dst} := M[p_q]$ and `store q i` sets $M[p_q] := r_i$. Pointers can be set to an integer constant, copied, incremented, decremented, and compared with a conditional jump; real registers can be tested for $\le 0$ with a conditional jump. `accept` and `reject` halt.
--
--   **Cost.** Every executed instruction costs one unit, including a memory access through a pointer, whatever the value of the pointer. A run of $T$ steps of a program whose largest pointer constant is $K$ keeps every pointer in $[-K-T, K+T]$, because pointers change by at most one per step; this is what makes the model polynomially equivalent to the tape machine, since a tape machine can simulate a memory access by walking its head to the addressed cell at a cost linear in the distance.
--
--   **Semantics and decision predicate.** `RAMStep` is one execution step, `RAMRun R x t` the configuration after $t$ steps from input memory $x$ with all registers zero, `RAMHaltedWith R s b` says the current instruction is `accept` (for $b$ true) or `reject` (for $b$ false), and `RAMDecidesInTime R x T b` says that the machine halts with output $b$ within $T$ steps. These mirror the definitions of the tape machine exactly, so the two models can be compared on the same inputs, in particular on `encodeLP A b`.
--
--   **Purpose.** Algorithms in the literature on Smale's ninth problem are written for a random-access machine over the reals. The compilation theorem of the mission shows that any such algorithm running in $T$ steps yields a tape program running in $O(T^2)$ steps, so the goal theorem in the tape model follows from a strongly polynomial algorithm in this random-access model.
-- source:
--   S. Smale, Mathematical problems for the next century, Math. Intelligencer 20(2):7-15, 1998, Problem 9 (real RAM formulation); L. Blum, F. Cucker, M. Shub, S. Smale, Complexity and Real Computation, Springer 1998, Chapter 3 (machines over R with indirect addressing).

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Iterate

/-!
A pointer machine over the real numbers: finitely many real registers,
finitely many integer pointer registers, and a random-access memory
`ℤ → ℝ`, with unit cost per instruction.

Source: the "real RAM" formulation of Smale's 9th problem (S. Smale,
*Mathematical problems for the next century*, Math. Intelligencer 20(2):7–15,
1998, Problem 9) and the random-access variant of the Blum–Shub–Smale
machine (L. Blum, F. Cucker, M. Shub, S. Smale, *Complexity and Real
Computation*, Springer 1998, Chapter 3, machines with indirect addressing).

Compared with the tape machine `Definitions.Def_SmaleNinth_BSSMachine`, this
model has random access to memory through pointer registers. Pointers are
manipulated only by setting to a constant, copying, incrementing and
decrementing, and comparing, so in `T` steps every pointer stays within
`T` plus the largest constant of the program of `0`; a tape machine can
therefore simulate a run of `T` steps with `O(T²)` steps by walking its
head to each accessed cell. This is the content of the compilation theorem
of the mission, which reduces the tape-machine form of Smale's problem to
the random-access form in which algorithms are usually written.
-/

namespace SmaleNinth

/-- An instruction of the real pointer machine. Real registers are indexed
by `ℕ`, pointer registers by `ℕ`; memory is indexed by `ℤ`. -/
inductive RAMInstr : Type
  /-- `r[dst] := c` — load a machine constant (an arbitrary real). -/
  | const (dst : ℕ) (c : ℝ)
  /-- `r[dst] := r[i] + r[j]`. -/
  | add (dst i j : ℕ)
  /-- `r[dst] := r[i] − r[j]`. -/
  | sub (dst i j : ℕ)
  /-- `r[dst] := r[i] * r[j]`. -/
  | mul (dst i j : ℕ)
  /-- `r[dst] := r[i] / r[j]` (Lean-total: division by zero yields `0`). -/
  | div (dst i j : ℕ)
  /-- `r[dst] := M[p[q]]` — indirect load through pointer `q`. -/
  | load (dst q : ℕ)
  /-- `M[p[q]] := r[i]` — indirect store through pointer `q`. -/
  | store (q i : ℕ)
  /-- `p[q] := c` — set a pointer to an integer constant. -/
  | pset (q : ℕ) (c : ℤ)
  /-- `p[q] := p[q']`. -/
  | pcopy (q q' : ℕ)
  /-- `p[q] := p[q] + 1`. -/
  | pinc (q : ℕ)
  /-- `p[q] := p[q] − 1`. -/
  | pdec (q : ℕ)
  /-- If `r[i] ≤ 0` jump to instruction `target`, else fall through. -/
  | jle (i : ℕ) (target : ℕ)
  /-- If `p[q] ≤ p[q']` jump to instruction `target`, else fall through. -/
  | pjle (q q' : ℕ) (target : ℕ)
  /-- Halt and accept. -/
  | accept
  /-- Halt and reject. -/
  | reject

/-- A program of the real pointer machine: a finite list of instructions,
executed from position `0`. -/
abbrev RAMProgram := List RAMInstr

/-- A configuration: program counter, real registers, pointer registers, memory. -/
structure RAMConfig where
  /-- The program counter. -/
  pc : ℕ
  /-- The real registers (all initially `0`). -/
  regs : ℕ → ℝ
  /-- The pointer registers (all initially `0`). -/
  ptrs : ℕ → ℤ
  /-- The random-access memory (initially the input). -/
  mem : ℤ → ℝ

/-- One execution step. A configuration whose `pc` carries `accept`/`reject`
(or points outside the program) is halted: the step leaves it unchanged. -/
noncomputable def RAMStep (R : RAMProgram) (s : RAMConfig) : RAMConfig :=
  match R[s.pc]? with
  | none => s
  | some ins =>
    match ins with
    | .const dst c => ⟨s.pc + 1, Function.update s.regs dst c, s.ptrs, s.mem⟩
    | .add dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i + s.regs j), s.ptrs, s.mem⟩
    | .sub dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i - s.regs j), s.ptrs, s.mem⟩
    | .mul dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i * s.regs j), s.ptrs, s.mem⟩
    | .div dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i / s.regs j), s.ptrs, s.mem⟩
    | .load dst q => ⟨s.pc + 1, Function.update s.regs dst (s.mem (s.ptrs q)), s.ptrs, s.mem⟩
    | .store q i => ⟨s.pc + 1, s.regs, s.ptrs, Function.update s.mem (s.ptrs q) (s.regs i)⟩
    | .pset q c => ⟨s.pc + 1, s.regs, Function.update s.ptrs q c, s.mem⟩
    | .pcopy q q' => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q'), s.mem⟩
    | .pinc q => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q + 1), s.mem⟩
    | .pdec q => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q - 1), s.mem⟩
    | .jle i target => if s.regs i ≤ 0 then ⟨target, s.regs, s.ptrs, s.mem⟩ else
        ⟨s.pc + 1, s.regs, s.ptrs, s.mem⟩
    | .pjle q q' target => if s.ptrs q ≤ s.ptrs q' then ⟨target, s.regs, s.ptrs, s.mem⟩ else
        ⟨s.pc + 1, s.regs, s.ptrs, s.mem⟩
    | .accept => s
    | .reject => s

/-- The configuration reached after `t` steps of `R` from input memory `x`
(program counter `0`, all registers `0`). -/
noncomputable def RAMRun (R : RAMProgram) (x : ℤ → ℝ) (t : ℕ) : RAMConfig :=
  (RAMStep R)^[t] ⟨0, fun _ => 0, fun _ => 0, x⟩

/-- The configuration `s` is halted with boolean output `b`. -/
def RAMHaltedWith (R : RAMProgram) (s : RAMConfig) (b : Bool) : Prop :=
  R[s.pc]? = some (if b then RAMInstr.accept else RAMInstr.reject)

/-- `R`, run on input memory `x`, halts with output `b` within `T` steps. -/
def RAMDecidesInTime (R : RAMProgram) (x : ℤ → ℝ) (T : ℕ) (b : Bool) : Prop :=
  ∃ t ≤ T, RAMHaltedWith R (RAMRun R x t) b

end SmaleNinth


