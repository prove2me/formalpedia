-- Prove2me | Definitions.Def_ExactDFTRefine_Main_RAM
-- name    : ExactDFTRefine_Main_RAM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:00:28.406898+00:00
-- url     : https://prove2.me/theorems/7b5b8bd0-3b97-4be0-8e15-44adbf478373
-- title:
--   The exact complex-arithmetic RAM of §2: instructions, runs, the root-order/transform program pair, work, the integer bound, and the positive-sign DFT of Eq. (1)
-- statement:
--   For $m \ge 1$ let $\zeta_m = \exp(2\pi i/m)$. The **discrete Fourier transform** of Eq. (1) is the positive-sign, unnormalized transform
--   $$(\mathrm{DFT}_n x)_j = \sum_{k=0}^{n-1} \zeta_n^{jk} x_k, \qquad 0 \le j < n,$$
--   for $x \in \mathbb C^n$.
--
--   The **exact complex-arithmetic RAM** has a program counter, integer registers $\mathrm{ireg}_0, \mathrm{ireg}_1, \dots$, an integer array memory $\mathrm{imem}$ indexed by $\mathbb Z$, exact complex scalar registers $\mathrm{creg}_0, \mathrm{creg}_1, \dots$ and an exact complex array memory $\mathrm{cmem}$ indexed by $\mathbb Z$. A **program** is a fixed finite list of instructions, executed from position $0$:
--
--   - integer words: a literal $k \in \mathbb Z$; $+$, $-$, $\times$, Euclidean division and remainder of two registers (division by $0$ gives $0$, remainder by $0$ gives the dividend); reading and writing $\mathrm{imem}$ at the address held in an integer register;
--   - scalars: a Gaussian-rational literal $a + b i$ ($a, b \in \mathbb Q$, of unrestricted magnitude); copying an integer register into a scalar register; exact $+$, $-$, $\times$, $\div$ of scalar registers (division by the scalar $0$ leaves the machine stuck: it never halts); reading and writing $\mathrm{cmem}$ at the address held in an integer register;
--   - control: unconditional jump, jumps on $=$ and $<$ of two integer registers, and $\mathrm{halt}$.
--
--   There is no instruction from scalars to integers or to control flow (no comparison, rounding, real part or conversion of a scalar), and no instruction computes a transform, a convolution or a polynomial product. Each executed instruction, including $\mathrm{halt}$, costs one unit; a program counter outside the program leaves the machine stuck.
--
--   A **run** of a program pair $(P_1, P_2)$ on length $n$ and input $x \in \mathbb C^n$, with **work** $W$ and integer bound $(n+2)^c$ (`DFTRun P₁ P₂ c n x W`), means: the root-order program $P_1$, started with $\mathrm{ireg}_0 = n$ and everything else $0$, halts after $k_1$ instructions with $\mathrm{ireg}_0 = D$, a natural number with $1 \le D < 1024 n^3$; the **root primitive** supplies $\zeta_D$; the transform program $P_2$, started with $\mathrm{ireg}_0 = n$, $\mathrm{ireg}_1 = D$, $\mathrm{creg}_0 = \zeta_D$, $\mathrm{cmem}_k = x_k$ for $0 \le k < n$ and everything else $0$, halts after $k_2$ instructions with $\mathrm{cmem}_j = (\mathrm{DFT}_n x)_j$ for every $0 \le j < n$; at every step of both programs every integer register and every integer memory cell (hence every address used) has absolute value at most $(n+2)^c$; and $W = k_1 + 1 + k_2$, the $1$ being the root primitive.
--
--   **Formalization Note.** `Instr`, `State`, `exec`, `step`, `runFor` (the $k$-fold step), `HaltsAt P s k` (halted after exactly $k$ steps, not before), `IntBounded`, `initRootOrder`, `initTransform`, `zeta`, `dft`, `DFTRun`. The paper summarizes the model of OpenAI's reference specification [11] without reproducing it; this machine has every capability Section 2 names (exact scalar arithmetic with unrestricted coefficients, integer words, arrays, index operations, one root primitive, a step-counting semantics) and none that would let exact scalars pack integers or shortcut the transform.
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 2, §2 (the computational model, after OpenAI [11]) and Eq. (1)

import Mathlib

/-!
# The exact complex-arithmetic RAM model, its two-program runs, and the DFT of Eq. (1)

Yao, Liu, *A Numerical Refinement of an Exact Discrete Fourier Transform Bound*,
arXiv:2611.01257v1, p. 2, §2 (the model, after OpenAI's exact RAM model [11]) and Eq. (1).

Conventions.
* A **program** is a finite list of instructions, executed from position `0`. It is fixed: it
  does not depend on the transform length `n`.
* A **state** has integer registers `ireg : ℕ → ℤ`, an integer array memory `imem : ℤ → ℤ`
  addressed by integers, exact complex scalar registers `creg : ℕ → ℂ`, an exact complex array
  memory `cmem : ℤ → ℂ` addressed by integers, a program counter and a halted flag.
* Integer-word instructions: literal, `+`, `−`, `×`, Lean's `Int` division and remainder
  (Euclidean, with `a / 0 = 0` and `a % 0 = a`), array read and write at the address held in
  an integer register, unconditional jump, and jumps on `=` and `<` of integer registers.
* Scalar instructions: a Gaussian-rational literal `re + im·i` (`re im : ℚ`, of unrestricted
  magnitude), the conversion of an integer register to a scalar, exact `+`, `−`, `×`, `÷` of
  scalar registers, and scalar array read and write at the address held in an integer register.
  A division by the scalar `0` leaves the machine **stuck** (it never halts).
* There is no instruction from scalars to integers or to control: no comparison, rounding, real
  or imaginary part, or conversion of a scalar. No instruction computes a transform, a
  convolution or a polynomial product.
* Every executed instruction, including `halt`, costs one unit. An instruction counter outside
  the program leaves the machine stuck. Only `halt` halts.
* A **run on length `n` and input `x`**: the root-order program `P₁` starts with `ireg 0 = n` and
  everything else `0`, and halts with the order `D = ireg 0`, which must satisfy
  `1 ≤ D < 1024 n³`. The root primitive (one unit of work) supplies `ζ_D = exp(2πi/D)`. The
  transform program `P₂` starts with `ireg 0 = n`, `ireg 1 = D`, `creg 0 = ζ_D`,
  `cmem k = x_k` for `0 ≤ k < n`, and everything else `0`; at its halt `cmem j` (`0 ≤ j < n`)
  is the output. The work is the number of executed instructions of both programs plus one
  for the root primitive. Every integer value held in any integer register or integer memory
  cell at any step of either program (so every address used) is at most `(n + 2)^c` in
  absolute value.
-/

namespace ExactDFTRefine.Main

/-- `ζ_m = exp(2πi/m)`, the canonical primitive `m`-th root of unity. -/
noncomputable def zeta (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

/-- The positive-sign, unnormalized discrete Fourier transform of Eq. (1):
`(DFT_n x)_j = ∑_{k=0}^{n-1} ζ_n^{jk} x_k`, `0 ≤ j < n`. -/
noncomputable def dft (n : ℕ) (x : Fin n → ℂ) (j : Fin n) : ℂ :=
  ∑ k : Fin n, zeta n ^ (j.val * k.val) * x k

/-- An instruction of the exact complex-arithmetic RAM. Register operands are register
indices (`ℕ`); jump targets are program positions. -/
inductive Instr where
  /-- `ireg d := k`. -/
  | iconst (d : ℕ) (k : ℤ)
  /-- `ireg d := ireg a + ireg b`. -/
  | iadd (d a b : ℕ)
  /-- `ireg d := ireg a - ireg b`. -/
  | isub (d a b : ℕ)
  /-- `ireg d := ireg a * ireg b`. -/
  | imul (d a b : ℕ)
  /-- `ireg d := ireg a / ireg b` (Lean's `Int` division). -/
  | idiv (d a b : ℕ)
  /-- `ireg d := ireg a % ireg b` (Lean's `Int` remainder). -/
  | imod (d a b : ℕ)
  /-- `ireg d := imem (ireg a)`. -/
  | iload (d a : ℕ)
  /-- `imem (ireg a) := ireg s`. -/
  | istore (a s : ℕ)
  /-- `creg d := re + im·i`. -/
  | cconst (d : ℕ) (re im : ℚ)
  /-- `creg d := ireg a` (an integer viewed as a scalar). -/
  | cofInt (d a : ℕ)
  /-- `creg d := creg a + creg b`. -/
  | cadd (d a b : ℕ)
  /-- `creg d := creg a - creg b`. -/
  | csub (d a b : ℕ)
  /-- `creg d := creg a * creg b`. -/
  | cmul (d a b : ℕ)
  /-- `creg d := creg a / creg b`; stuck when `creg b = 0`. -/
  | cdiv (d a b : ℕ)
  /-- `creg d := cmem (ireg a)`. -/
  | cload (d a : ℕ)
  /-- `cmem (ireg a) := creg s`. -/
  | cstore (a s : ℕ)
  /-- Jump to position `target`. -/
  | jmp (target : ℕ)
  /-- Jump to `target` if `ireg a = ireg b`, else continue. -/
  | jeq (a b target : ℕ)
  /-- Jump to `target` if `ireg a < ireg b`, else continue. -/
  | jlt (a b target : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions. -/
abbrev Program := List Instr

/-- A machine state. -/
structure State where
  /-- Program counter. -/
  pc : ℕ
  /-- Integer registers. -/
  ireg : ℕ → ℤ
  /-- Integer array memory. -/
  imem : ℤ → ℤ
  /-- Exact complex scalar registers. -/
  creg : ℕ → ℂ
  /-- Exact complex scalar array memory. -/
  cmem : ℤ → ℂ
  /-- Halted flag. -/
  halted : Bool

open Classical in
/-- Execute one instruction `i` in state `s` (the instruction at `s.pc`). -/
noncomputable def exec (i : Instr) (s : State) : State :=
  match i with
  | .iconst d k => { s with pc := s.pc + 1, ireg := Function.update s.ireg d k }
  | .iadd d a b =>
      { s with pc := s.pc + 1, ireg := Function.update s.ireg d (s.ireg a + s.ireg b) }
  | .isub d a b =>
      { s with pc := s.pc + 1, ireg := Function.update s.ireg d (s.ireg a - s.ireg b) }
  | .imul d a b =>
      { s with pc := s.pc + 1, ireg := Function.update s.ireg d (s.ireg a * s.ireg b) }
  | .idiv d a b =>
      { s with pc := s.pc + 1, ireg := Function.update s.ireg d (s.ireg a / s.ireg b) }
  | .imod d a b =>
      { s with pc := s.pc + 1, ireg := Function.update s.ireg d (s.ireg a % s.ireg b) }
  | .iload d a =>
      { s with pc := s.pc + 1, ireg := Function.update s.ireg d (s.imem (s.ireg a)) }
  | .istore a v =>
      { s with pc := s.pc + 1, imem := Function.update s.imem (s.ireg a) (s.ireg v) }
  | .cconst d re im =>
      { s with pc := s.pc + 1, creg := Function.update s.creg d (⟨(re : ℝ), (im : ℝ)⟩ : ℂ) }
  | .cofInt d a =>
      { s with pc := s.pc + 1, creg := Function.update s.creg d ((s.ireg a : ℤ) : ℂ) }
  | .cadd d a b =>
      { s with pc := s.pc + 1, creg := Function.update s.creg d (s.creg a + s.creg b) }
  | .csub d a b =>
      { s with pc := s.pc + 1, creg := Function.update s.creg d (s.creg a - s.creg b) }
  | .cmul d a b =>
      { s with pc := s.pc + 1, creg := Function.update s.creg d (s.creg a * s.creg b) }
  | .cdiv d a b =>
      if s.creg b = 0 then s
      else { s with pc := s.pc + 1, creg := Function.update s.creg d (s.creg a / s.creg b) }
  | .cload d a =>
      { s with pc := s.pc + 1, creg := Function.update s.creg d (s.cmem (s.ireg a)) }
  | .cstore a v =>
      { s with pc := s.pc + 1, cmem := Function.update s.cmem (s.ireg a) (s.creg v) }
  | .jmp target => { s with pc := target }
  | .jeq a b target => { s with pc := if s.ireg a = s.ireg b then target else s.pc + 1 }
  | .jlt a b target => { s with pc := if s.ireg a < s.ireg b then target else s.pc + 1 }
  | .halt => { s with halted := true }

/-- One step of program `P`. A halted state does not change; a counter outside the program
leaves the state unchanged (stuck). -/
noncomputable def step (P : Program) (s : State) : State :=
  if s.halted then s
  else match P[s.pc]? with
    | none => s
    | some i => exec i s

/-- The state after `k` steps of `P` from `s`. -/
noncomputable def runFor (P : Program) (s : State) (k : ℕ) : State :=
  (step P)^[k] s

/-- `P` started in `s` halts after exactly `k` executed instructions (the last one `halt`). -/
def HaltsAt (P : Program) (s : State) (k : ℕ) : Prop :=
  (runFor P s k).halted = true ∧ ∀ j < k, (runFor P s j).halted = false

/-- Every integer register and every integer memory cell of `s` is at most `M` in absolute
value. -/
def IntBounded (s : State) (M : ℤ) : Prop :=
  (∀ r : ℕ, |s.ireg r| ≤ M) ∧ (∀ a : ℤ, |s.imem a| ≤ M)

/-- The initial state of the root-order program on length `n`: `ireg 0 = n`, everything else
`0`. -/
def initRootOrder (n : ℕ) : State where
  pc := 0
  ireg := fun r => if r = 0 then (n : ℤ) else 0
  imem := fun _ => 0
  creg := fun _ => 0
  cmem := fun _ => 0
  halted := false

/-- The initial state of the transform program on length `n`, root order `D` and input `x`:
`ireg 0 = n`, `ireg 1 = D`, `creg 0 = ζ_D` (supplied by the root primitive),
`cmem k = x_k` for `0 ≤ k < n`, everything else `0`. -/
noncomputable def initTransform (n D : ℕ) (x : Fin n → ℂ) : State where
  pc := 0
  ireg := fun r => if r = 0 then (n : ℤ) else if r = 1 then (D : ℤ) else 0
  imem := fun _ => 0
  creg := fun r => if r = 0 then zeta D else 0
  cmem := fun a => if h : 0 ≤ a ∧ a < (n : ℤ) then x ⟨a.toNat, by omega⟩ else 0
  halted := false

/-- **The run of the program pair `(P₁, P₂)` on length `n` and input `x` computes `DFT_n x`
with total work `W` and integer bound `(n + 2)^c`.**

The root-order program `P₁` halts after `k₁` instructions with `ireg 0 = D`,
`1 ≤ D < 1024 n³`; the root primitive supplies `ζ_D` (one unit); the transform program `P₂`
halts after `k₂` instructions with `cmem j = (DFT_n x)_j` for every `0 ≤ j < n`; at every step
of both programs every integer register and integer memory cell is at most `(n + 2)^c` in
absolute value; and `W = k₁ + 1 + k₂`. -/
def DFTRun (P₁ P₂ : Program) (c n : ℕ) (x : Fin n → ℂ) (W : ℕ) : Prop :=
  ∃ k₁ k₂ D : ℕ,
    HaltsAt P₁ (initRootOrder n) k₁ ∧
    (runFor P₁ (initRootOrder n) k₁).ireg 0 = (D : ℤ) ∧
    1 ≤ D ∧ D < 1024 * n ^ 3 ∧
    HaltsAt P₂ (initTransform n D x) k₂ ∧
    (∀ j : Fin n, (runFor P₂ (initTransform n D x) k₂).cmem (j.val : ℤ) = dft n x j) ∧
    (∀ i ≤ k₁, IntBounded (runFor P₁ (initRootOrder n) i) (((n : ℤ) + 2) ^ c)) ∧
    (∀ i ≤ k₂, IntBounded (runFor P₂ (initTransform n D x) i) (((n : ℤ) + 2) ^ c)) ∧
    W = k₁ + 1 + k₂

end ExactDFTRefine.Main


