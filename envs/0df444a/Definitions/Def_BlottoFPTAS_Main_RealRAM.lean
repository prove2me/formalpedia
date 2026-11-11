-- Prove2me | Definitions.Def_BlottoFPTAS_Main_RealRAM
-- name    : BlottoFPTAS_Main_RealRAM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:04.229672+00:00
-- url     : https://prove2.me/theorems/5be507bb-b9a7-4f0f-b082-b92130ee122e
-- title:
--   The unit-cost randomized real RAM with rational literals, indexed storage and Unif[0,1] draws; runs, outputs and the law of a sampler
-- statement:
--   The **real-RAM model** of §2.2: exact $+,-,\times,\div$ and comparisons of reals at unit cost, independent exact $\mathrm{Unif}[0,1]$ samples at unit cost, indexed storage and control; floors and continued fractions are computed from these primitives and logarithms and exponentials are not evaluated (App. F.4).
--
--   The machine extends the published real-RAM core `SmaleNinth.RAMInstr` (exact arithmetic on real registers, real literals, indirect real memory $M[p_q]$ through integer pointer registers, pointer set/copy/increment/decrement, comparison jumps on reals and pointers) by: pointer addition and subtraction; `toPtr`, which copies a real register holding an **integer** into a pointer register (on a non-integer the machine is stuck forever, so it yields neither a floor nor an integrality test); `ofPtr`, pointer to real; `unif`, which loads the next cell of the uniform tape; and `halt`. A program is **admissible** when every real literal is **rational** and the core's `accept`/`reject` do not occur, and **deterministic** when it contains no `unif` instruction. Each executed instruction costs one unit; only `halt` halts.
--
--   A run on the input list $xs$ starts with memory cell $0$ holding $|xs|$ and cells $1,\dots,|xs|$ holding $xs$; its output is the list of memory cells $-1,-2,\dots,-\ell$ at the first halted state, with $\ell$ the value of pointer register $0$. The uniform tape is the product of $\mathrm{Unif}[0,1]$ laws on $\mathbb R^{\mathbb N}$; a tape is in the support when all its cells lie in $[0,1]$. The **law** of a sampler program $S$ on a description $d$ is the pushforward of the uniform tape under $\omega\mapsto$ (the allocation formed by the first $n$ output entries).
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 6, §2.2 (real-RAM model); p. 72, App. F.4

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace BlottoFPTAS.Main

/-!
# The real-RAM model (§2.2, p. 6; App. F.4, p. 72)

"Each addition, subtraction, multiplication, division, and comparison of exact real numbers has
unit cost. The model also provides independent exact samples from Unif[0, 1] at unit cost."
App. F.4 adds indexed storage and control; floors and continued fractions are computed from these
primitives, and logarithms and exponentials are not evaluated.

The machine extends the published core `SmaleNinth.RAMInstr` (exact `+ − × ÷` on real registers,
real literals, indirect real memory `M[p[q]]` through integer pointer registers, pointer
set/copy/increment/decrement, comparison jumps on reals and on pointers) with:
* `padd`, `psub`: pointer arithmetic `p[d] := p[a] ± p[b]` (indexed storage);
* `toPtr d r`: `p[d] := r[r]` when the real register `r[r]` holds an integer. On a non-integer the
  machine is **stuck** (it repeats the instruction forever and never halts), so the instruction
  gives no floor and no integrality test;
* `ofPtr d p`: `r[d] := p[p]`;
* `unif d`: `r[d] :=` the next cell of the uniform tape (independent Unif[0, 1] values);
* `halt`.

`Admissible` requires every real literal to be **rational** (an arbitrary real literal could
encode an oracle) and forbids the core's `accept`/`reject`. There is no floor, `exp`, `log` or
square root. Division by zero gives `0` (Lean's convention; never needed). Every executed
instruction costs one unit; an instruction counter outside the program is stuck. Only `halt`
halts.

**Input and output layout.** A run on the input list `xs` starts with all registers and pointers
`0`, memory cell `0` holding the length of `xs` and cells `1, …, |xs|` holding `xs`; every other
cell is `0`. At the first halted state, the output is the list of the real memory cells
`-1, -2, …, -ℓ`, where `ℓ` is the value of pointer register `0` (`ℓ ≤ 0` gives the empty list).
-/

namespace RealRAM

/-- An instruction of the real RAM. -/
inductive Instr where
  /-- A `SmaleNinth` core instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `p[dst] := p[a] + p[b]`. -/
  | padd (dst a b : ℕ)
  /-- `p[dst] := p[a] - p[b]`. -/
  | psub (dst a b : ℕ)
  /-- `p[dst] := r[src]` if `r[src]` is an integer; stuck otherwise. -/
  | toPtr (dst src : ℕ)
  /-- `r[dst] := p[src]`. -/
  | ofPtr (dst src : ℕ)
  /-- `r[dst] :=` the next uniform tape value. -/
  | unif (dst : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The program is deterministic: it contains no uniform-draw instruction. -/
def Deterministic (P : Program) : Prop :=
  ∀ op ∈ P, ∀ d : ℕ, op ≠ .unif d

/-- The core table of `P` (extension instructions are placeholders, never executed by the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state. -/
structure State where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Position of the next unread uniform tape cell. -/
  cursor : ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Number of executed instructions. -/
  work : ℕ

/-- One step of `P` with uniform tape `ω`. A halted state does not change. -/
noncomputable def step (P : Program) (ω : ℕ → ℝ) (s : State) : State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.padd d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.psub d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.toPtr d a) =>
        if (s.core.regs a : ℝ) = (⌊s.core.regs a⌋ : ℝ) then
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs d ⌊s.core.regs a⌋ } }
        else { s with work := s.work + 1 }
    | some (.ofPtr d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.unif d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with regs := Function.update s.core.regs d (ω s.cursor) } }
    | some .halt => { t with halted := true }

/-- The initial state on input `xs`: memory cell `0` holds `|xs|`, cells `1, …, |xs|` hold `xs`. -/
noncomputable def initState (xs : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0,
    fun z => if z = 0 then (xs.length : ℝ) else if 0 < z then xs.getD (z.toNat - 1) 0 else 0⟩,
    0, false, 0⟩

/-- The state after `k` steps on input `xs` and tape `ω`. -/
noncomputable def run (P : Program) (xs : List ℝ) (ω : ℕ → ℝ) (k : ℕ) : State :=
  (step P ω)^[k] (initState xs)

/-- The run halts. -/
def Halts (P : Program) (xs : List ℝ) (ω : ℕ → ℝ) : Prop :=
  ∃ k : ℕ, (run P xs ω k).halted = true

/-- The run halts within `B` executed instructions. -/
def HaltsWithin (P : Program) (xs : List ℝ) (ω : ℕ → ℝ) (B : ℝ) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ B ∧ (run P xs ω k).halted = true

/-- The output list of a halted state: memory cells `-1, …, -ℓ`, `ℓ = p[0]`. -/
noncomputable def outputOf (s : State) : List ℝ :=
  List.ofFn fun i : Fin (s.core.ptrs 0).toNat => s.core.mem (-((i : ℤ) + 1))

open Classical in
/-- The output of the run (at its first halted state), `none` if it never halts. -/
noncomputable def output (P : Program) (xs : List ℝ) (ω : ℕ → ℝ) : Option (List ℝ) :=
  if h : ∃ k, (run P xs ω k).halted = true then some (outputOf (run P xs ω (Nat.find h)))
  else none

/-- The tape fed to a deterministic program (never read). -/
def zeroTape : ℕ → ℝ := fun _ => 0

/-- A tape in the support of the uniform tape: every cell lies in `[0, 1]`. -/
def TapeInSupport (ω : ℕ → ℝ) : Prop :=
  ∀ i, ω i ∈ Set.Icc (0 : ℝ) 1

/-- The uniform tape: independent Unif[0, 1] values. -/
noncomputable def uniformTape : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The allocation read from an output list: coordinate `i` is the `i`-th entry (`0` if
missing). -/
def toAlloc (n : ℕ) (out : Option (List ℝ)) : Fin n → ℝ :=
  fun i => (out.getD []).getD i 0

/-- The law of the allocation sampled by program `S` run on the description `d`: the pushforward
of the uniform tape under the output map. -/
noncomputable def law (S : Program) (d : List ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  uniformTape.map fun ω => toAlloc n (output S d ω)

end RealRAM

end BlottoFPTAS.Main


