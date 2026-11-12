-- Prove2me | Definitions.Def_SepQPTardos_Main_Machine
-- name    : SepQPTardos_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:10.282746+00:00
-- url     : https://prove2.me/theorems/291ceba9-78ed-408a-98e0-fa9e26b3bf00
-- title:
--   Admissible real-RAM programs, memory layouts, and runs with bounded steps and bounded intermediate encodings
-- statement:
--   The computational model is the published real pointer machine (`SmaleNinth_RealRAM`): finitely many real registers, integer pointer registers that are set to program constants, copied, incremented, decremented and compared, a memory $\mathbb Z\to\mathbb R$ addressed through pointers, the operations $+,-,\times,\div$ on reals (with $x/0=0$), the test $r\le 0$, and `accept`/`reject`. Every executed instruction costs one unit. There is no floor, no conversion of a real into a pointer, and no instruction that solves an optimisation problem.
--
--   1. A program is **admissible** if every real constant it loads is an integer. A real constant could otherwise encode an arbitrary table; the restriction is on the code, never on the inputs.
--   2. The **input memory** of a list $x_0,\dots,x_{k-1}$ holds $x_i$ in cell $i$ and $0$ in every other cell. A vector is read from $n$ consecutive cells starting at a given address.
--   3. A configuration has **encoding length at most** $B$ if every real register and every memory cell holds a rational of encoding length at most $B$.
--   4. A program $R$ **computes within** $T$ steps and length $B$ an output property $\mathrm{Out}$ on input memory $x$ if the run of $R$ on $x$ reaches `accept` at some step $t\le T$, the memory at step $t$ satisfies $\mathrm{Out}$, and every configuration of this same run at steps $0,\dots,t$ has encoding length at most $B$. A halted configuration never changes, so the memory at step $t$ is the output of the run.
--
--   These notions turn "an algorithm with $\mathrm{poly}(\cdot)$ basic operations and polynomial intermediate encodings" into a statement about one fixed program.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §1, p. 2 ("basic operations are addition, subtraction, multiplication, division, and comparison of rational numbers"); Theorem 1.1, p. 2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SepQPTardos_Main_Encoding

namespace SepQPTardos.Main

/-!
# The arithmetic model: admissible real-RAM programs, layouts, halting and trace length

Cui–Li–Miao, STOC 2027 submission #829 (October 2026), §1, p. 2: "basic operations are
addition, subtraction, multiplication, division, and comparison of rational numbers".

The machine is the published real pointer machine `SmaleNinth.RAMProgram` (real registers,
integer pointer registers moving by `±1` or set to program constants, memory `ℤ → ℝ`,
`+ − × ÷` with `x / 0 = 0`, the test `r ≤ 0`, pointer comparison, `accept`/`reject`), one unit
of cost per executed instruction. It has no floor, no real-to-pointer conversion and no
instruction that solves an LP, a QP or computes a compression.

* `Admissible R`: every real constant loaded by `const` is an integer, so a program cannot hide
  information in a real constant. Only the code is restricted, never the inputs.
* `listMem xs`: input memory holding the list `xs` in cells `0, 1, …`, all other cells `0`.
* `readVec mem off n`: the vector of the `n` cells `off, …, off + n − 1`.
* `ConfigLenLe s B`: every real register and every memory cell of `s` holds a rational of
  encoding length at most `B`.
* `ComputesWithin R x T B Out`: run on input memory `x`, `R` reaches `accept` at some step
  `t ≤ T`, the memory at that step satisfies `Out`, and every configuration of the run up to
  step `t` satisfies `ConfigLenLe · B`. A halted configuration is never changed again, so the
  memory at step `t` is the output of the run.
-/

open SmaleNinth

/-- Admissible program: every `const` instruction loads an integer. -/
def Admissible (R : RAMProgram) : Prop :=
  ∀ ins ∈ R, ∀ (dst : ℕ) (c : ℝ), ins = RAMInstr.const dst c → ∃ z : ℤ, c = (z : ℝ)

/-- Memory holding `xs` in cells `0, 1, …, |xs| − 1`; every other cell (including negative
addresses) holds `0`. -/
noncomputable def listMem (xs : List ℝ) : ℤ → ℝ :=
  fun z => if 0 ≤ z then xs.getD z.toNat 0 else 0

/-- The vector stored in the `n` consecutive cells starting at address `off`. -/
def readVec (mem : ℤ → ℝ) (off n : ℕ) : Fin n → ℝ :=
  fun i => mem ((off : ℤ) + (i : ℕ))

/-- A real vector as a list, in index order. -/
def vecList {n : ℕ} (v : Fin n → ℝ) : List ℝ := List.ofFn v

/-- A real matrix as a list, row-major. -/
def matList {p n : ℕ} (M : Matrix (Fin p) (Fin n) ℝ) : List ℝ :=
  (List.ofFn fun i => List.ofFn (M i)).flatten

/-- Every real register and every memory cell of `s` is a rational of length at most `B`. -/
def ConfigLenLe (s : RAMConfig) (B : ℕ) : Prop :=
  (∀ i, RealLenLe (s.regs i) B) ∧ ∀ z, RealLenLe (s.mem z) B

/-- `R` on input memory `x` halts at `accept` within `T` steps with output memory satisfying
`Out`, and every intermediate configuration of this same run has all its numbers of encoding
length at most `B`. -/
def ComputesWithin (R : RAMProgram) (x : ℤ → ℝ) (T B : ℕ) (Out : (ℤ → ℝ) → Prop) : Prop :=
  ∃ t ≤ T, RAMHaltedWith R (RAMRun R x t) true ∧ Out (RAMRun R x t).mem ∧
    ∀ s ≤ t, ConfigLenLe (RAMRun R x s) B

end SepQPTardos.Main


