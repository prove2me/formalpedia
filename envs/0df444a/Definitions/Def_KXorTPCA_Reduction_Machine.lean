-- Prove2me | Definitions.Def_KXorTPCA_Reduction_Machine
-- name    : KXorTPCA_Reduction_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:18:30.060433+00:00
-- url     : https://prove2.me/theorems/e59d0a62-a01e-4d0d-b9d1-de13265896e1
-- title:
--   The randomized real RAM: programs, runs, outputs and polynomial time (§C.3)
-- statement:
--   The paper's algorithms are "polynomial-time (possibly randomized) algorithms" (§C.3); it names no machine. This definition fixes one: the published unit-cost **real RAM** core `SmaleNinth.RAMInstr` (real registers, integer pointer registers, a memory $M:\mathbb Z\to\mathbb R$; real constants, $+,-,\times,\div$, indirect load/store through pointers, pointer set/copy/increment/decrement, comparison jumps, `accept`, `reject`), extended by
--
--   - `unif d`: register $d$ receives the next cell of a tape of i.i.d. $\mathrm{Uniform}(0,1)$ values;
--   - `gauss d`: register $d$ receives the next cell of an independent tape of i.i.d. $N(0,1)$ values;
--   - `exp`, `log`, `sqrt` of a real register.
--
--   A **program** is a finite list of instructions, the same for every input. On an input memory image $y$ (an encoded instance, whose cell $0$ holds the dimension $n$) and a pair of tapes $\omega=(u,g)$, the run starts at instruction $0$ with all registers and pointers $0$; it is **halted** when the program counter points at `accept` or `reject`. The **tape law** is $\bigotimes_{\mathbb N}\mathrm{Uniform}(0,1)\otimes\bigotimes_{\mathbb N}N(0,1)$.
--
--   Outputs: the **accept bit** ($A(Y)=1$ iff the run halts in `accept`); the **final memory** (the output of a reduction is its whole final memory, which must be the encoding of the output instance); and the **estimate** $\hat x\in\{\pm1\}^n$ with $\hat x_i=+1$ iff final memory cell $i$ is $\ge 0$, $i=1,\dots,n$.
--
--   A program $P$ is **polynomial-time** if there are constants $C,r\in\mathbb N$ such that on every memory image with cell $0$ equal to $n$ and every pair of tapes it halts within
--
--   $$C\,n^{r}+C$$
--
--   steps. Two auxiliary notions: interleaving two tape pairs into one (a program can see the randomness of another run and fresh randomness), and the probability of an event of $k$ independent tape pairs.
--
--   **Formalization Note** The time bound is worst case over all memory images with the given cell $0$ and over all tapes, not expected time; requiring it beyond the support of the instance laws changes no class (a program can clock itself). Real constants are allowed in programs. `log` and `sqrt` are Lean's total functions ($\log 0=0$, $\log(-x)=\log x$, $\sqrt{x}=0$ for $x<0$); division by $0$ gives $0$. A program counter outside the program is stuck and never halts.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), pp. 96–98 (PDF 99–101), §C.3 ('O(n^r)-time (possibly randomized) algorithm'); machine core: SmaleNinth_RealRAM

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false

open MeasureTheory

/-!
# The randomized real RAM of the mission (machine model of "polynomial-time algorithm")

G. Bresler, A. Harbuzova, *Average-Case Reductions for k-XOR and Tensor PCA*, arXiv:2601.19016
(copy sha256 6ec029a7…), §C.3, pp. 96–98: "a O(n^r)-time (possibly randomized) algorithm".
The paper names no machine. This one is the published unit-cost real RAM core
`SmaleNinth.RAMInstr` (real constants, `+ − × ÷`, indirect load/store through integer pointers,
pointer set/copy/increment/decrement, comparison jumps, `accept`/`reject`), extended (pattern of
`EasyRankOne.Secretary.Instr`) by
* `unif d`: `r[d] :=` the next cell of a tape of i.i.d. Uniform(0,1) values;
* `gauss d`: `r[d] :=` the next cell of an independent tape of i.i.d. N(0,1) values;
* `exp`, `log`, `sqrt` of a real register (Lean's total `Real.log`, `Real.sqrt`).

Conventions. The input is a memory image `y : ℤ → ℝ` (an encoded instance; cell `0` holds the
dimension). A run starts at program counter `0` with all registers and pointers `0`. A
configuration whose program counter carries `accept`/`reject` is halted; a program counter outside
the program is stuck and never halts. Outputs: the accept bit; the final memory (the output of a
reduction is its whole final memory, which must be the encoding of the output instance); and the
estimate `x̂ ∈ {±1}ⁿ` read from cells `1, …, n` (`x̂ᵢ = +1` iff cell `i` is `≥ 0`).
A program is polynomial-time if on every memory image whose cell `0` is `n` and on every pair of
tapes it halts within `C·nʳ + C` steps (one program for all `n`).
-/

namespace KXorTPCA.Reduction

/-- An instruction: a `SmaleNinth` real-RAM instruction, or one of the extensions. -/
inductive Instr where
  /-- A core real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `r[dst] :=` the next value of the uniform tape. -/
  | unif (dst : ℕ)
  /-- `r[dst] :=` the next value of the Gaussian tape. -/
  | gauss (dst : ℕ)
  /-- `r[dst] := exp r[src]`. -/
  | exp (dst src : ℕ)
  /-- `r[dst] := log r[src]` (Lean's `Real.log`: `log 0 = 0`, `log (-x) = log x`). -/
  | log (dst src : ℕ)
  /-- `r[dst] := sqrt r[src]` (Lean's `Real.sqrt`: `0` on negatives). -/
  | sqrt (dst src : ℕ)

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- The static core table of `P` (extension instructions become placeholders that the core never
executes). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A pair of random tapes: the uniform tape and the Gaussian tape. -/
abbrev Tapes := (ℕ → ℝ) × (ℕ → ℝ)

/-- The law of the tapes: i.i.d. Uniform(0,1) cells, and independently i.i.d. N(0,1) cells. -/
noncomputable def tapeLaw : Measure Tapes :=
  (Measure.infinitePi fun _ : ℕ => volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
    (Measure.infinitePi fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)

/-- A machine state: the core configuration and the two tape cursors. -/
structure MState where
  /-- Program counter, real registers, pointer registers, memory. -/
  core : SmaleNinth.RAMConfig
  /-- Cursor of the uniform tape. -/
  ucur : ℕ
  /-- Cursor of the Gaussian tape. -/
  gcur : ℕ

/-- Write `v` into real register `d` and advance the program counter. -/
def MState.setReg (s : MState) (d : ℕ) (v : ℝ) : MState :=
  { s with core := { s.core with pc := s.core.pc + 1, regs := Function.update s.core.regs d v } }

/-- One step of `P` with tapes `ω`. -/
noncomputable def step (P : Program) (ω : Tapes) (s : MState) : MState :=
  match P[s.core.pc]? with
  | none => s
  | some (.core _) => { s with core := SmaleNinth.RAMStep (coreProgram P) s.core }
  | some (.unif d) => { s.setReg d (ω.1 s.ucur) with ucur := s.ucur + 1 }
  | some (.gauss d) => { s.setReg d (ω.2 s.gcur) with gcur := s.gcur + 1 }
  | some (.exp d a) => s.setReg d (Real.exp (s.core.regs a))
  | some (.log d a) => s.setReg d (Real.log (s.core.regs a))
  | some (.sqrt d a) => s.setReg d (Real.sqrt (s.core.regs a))

/-- The state after `t` steps of `P` on input memory `y` with tapes `ω`. -/
noncomputable def run (P : Program) (y : ℤ → ℝ) (ω : Tapes) (t : ℕ) : MState :=
  (step P ω)^[t] ⟨⟨0, fun _ => 0, fun _ => 0, y⟩, 0, 0⟩

/-- The state `s` is halted with output bit `b` (`true` = accept). -/
def HaltedWith (P : Program) (s : MState) (b : Bool) : Prop :=
  P[s.core.pc]? = some (.core (if b then .accept else .reject))

/-- The state `s` is halted. -/
def IsHalted (P : Program) (s : MState) : Prop :=
  ∃ b, HaltedWith P s b

/-- `P` halts on `(y, ω)` within `T` steps. -/
def HaltsWithin (P : Program) (y : ℤ → ℝ) (ω : Tapes) (T : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ IsHalted P (run P y ω t)

/-- `P` accepts `(y, ω)`: the output bit `A(Y) = 1`. -/
def Accepts (P : Program) (y : ℤ → ℝ) (ω : Tapes) : Prop :=
  ∃ t, HaltedWith P (run P y ω t) true

open Classical in
/-- The final memory of `P` on `(y, ω)` (the zero memory if it never halts). -/
noncomputable def outMem (P : Program) (y : ℤ → ℝ) (ω : Tapes) : ℤ → ℝ :=
  if h : ∃ t, IsHalted P (run P y ω t) then (run P y ω (Nat.find h)).core.mem else fun _ => 0

/-- A signal vector `x ∈ {±1}ⁿ`. -/
abbrev Signal (n : ℕ) := Fin n → ℤˣ

/-- The estimate `x̂ ∈ {±1}ⁿ` output by `P`: `x̂ᵢ = +1` iff final memory cell `i + 1` is `≥ 0`
(`i = 0, …, n − 1`, i.e. cells `1, …, n`). -/
noncomputable def outVec (P : Program) (n : ℕ) (y : ℤ → ℝ) (ω : Tapes) : Signal n :=
  fun i => if 0 ≤ outMem P y ω ((i : ℤ) + 1) then 1 else -1

/-- Polynomial time: one program `P` and constants `C, r` such that on every memory image whose
cell `0` holds `n` and on every pair of tapes, `P` halts within `C·nʳ + C` steps. -/
def PolyTime (P : Program) : Prop :=
  ∃ C r : ℕ, ∀ n : ℕ, ∀ y : ℤ → ℝ, y 0 = n → ∀ ω : Tapes,
    HaltsWithin P y ω ((C : ℝ) * (n : ℝ) ^ r + C)

/-- Two tape pairs interleaved into one (even cells from `ω₁`, odd cells from `ω₂`): a program run
on `mixTapes ω₁ ω₂` sees the randomness `ω₁` of another run and fresh randomness `ω₂`. -/
def mixTapes (ω₁ ω₂ : Tapes) : Tapes :=
  (fun i => if i % 2 = 0 then ω₁.1 (i / 2) else ω₂.1 (i / 2),
   fun i => if i % 2 = 0 then ω₁.2 (i / 2) else ω₂.2 (i / 2))

/-- Probability of an event of `k` independent tape pairs. -/
noncomputable def probOver (k : ℕ) (E : (Fin k → Tapes) → Prop) : ℝ :=
  (Measure.pi (fun _ : Fin k => tapeLaw) {w | E w}).toReal

/-- The law of a random memory image built from two independent tape pairs. -/
noncomputable def lawOf2 (f : Tapes → Tapes → (ℤ → ℝ)) : Measure (ℤ → ℝ) :=
  (Measure.pi (fun _ : Fin 2 => tapeLaw)).map (fun w => f (w 0) (w 1))

end KXorTPCA.Reduction


