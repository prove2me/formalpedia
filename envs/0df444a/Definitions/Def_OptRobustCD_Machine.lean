-- Prove2me | Definitions.Def_OptRobustCD_Machine
-- name    : OptRobustCD_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:49:58.880898+00:00
-- url     : https://prove2.me/theorems/a870ce41-1745-4d7c-a683-2e36592332fa
-- title:
--   The randomized unit-cost real RAM: core RAM plus $\sqrt{\cdot}$, $\tanh$, uniform draws, exact-integer indexing and a matrix-vector oracle
-- statement:
--   The machine on which every running time of the paper is counted. The paper names none; it counts "arithmetic operations" (Theorem 4.2), "matrix-vector products" and "additional operations" (Lemma 5.9, Theorem 8.2), and calls algorithms "linear-time" or "nearly-linear time".
--
--   The machine is the published unit-cost real RAM `SmaleNinth.RAMInstr` (real registers, integer pointer registers, a real memory $\mathbb Z\to\mathbb R$ addressed through pointers; $+,-,\times,/$ on reals with $x/0=0$; arbitrary real constants; indirect load and store; pointer set, copy, increment, decrement; the branches "$r\le 0$" and "$p\le p'$"), extended by the following instructions, each costing one step:
--
--   1. `sqrt` and `tanh` on a real register;
--   2. `draw`: the next point of a draw tape $\omega\in[0,1]^{\mathbb N}$; tapes carry the product of uniform (Lebesgue) measures;
--   3. `idx`: copy a real register holding an **integer** into a pointer register (on a non-integer the machine is stuck forever), and `ofPtr`: copy a pointer into a real register;
--   4. `matvec`: one call of the matrix-vector oracle $f:\mathbb R^m\to\mathbb R^m$ of the run, reading $x_i=\mathrm{mem}[p_{\mathrm{src}}+i]$ and writing $f(x)_i$ to $\mathrm{mem}[p_{\mathrm{dst}}+i]$ for $i<m$; oracle calls are counted separately;
--   5. `halt`.
--
--   A run starts with program counter $0$, all registers $0$, and the input list in memory cells $0,1,\dots$. Its output is the memory block of length $p[1]$ starting at address $p[2]$ in the first halted state. $\mathrm{HaltsWithin}(P,O,l,B)$ says that on every tape the run halts within $B$ steps; $\mathrm{HaltsWithCounts}$ bounds oracle calls and other steps separately on one tape.
--
--   These are exactly the operations the paper's algorithm applies to reals: arithmetic and comparisons, square roots for normalizations, $\tanh$ for the randomized rounding of Definition 4.1, uniform random reals (proof of Lemma 4.10), indexing by vertex numbers, and matrix-vector products (Lemma 5.9, Theorem 8.2).
--
--   **Formalization Note** There is no floor, no rounding of non-integer reals, and no $\exp$, $\log$ or power instruction, so no bits of a non-integer real can be extracted in unit time. `idx` is needed because a graph is given by real vertex numbers and a linear-time algorithm must use them as addresses. The core's `accept`/`reject` never halt. `NoOracle P` says $P$ makes no oracle call.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 1.1 p.2 (pdf p.4); Theorem 4.2 p.16 (pdf p.18); Lemma 5.9 p.27 (pdf p.29); Theorem 8.2 p.37 (pdf p.39)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace OptRobustCD

/-!
# The randomized unit-cost real RAM in which the running times are counted

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…): Theorem 1.1 (p.2, pdf p.4,
"nearly-linear time algorithm"), Theorem 4.2 (p.16, pdf p.18, "arithmetic operations"),
Lemma 5.9 and Theorem 8.2 (pp.27, 37, pdf pp.29, 39, "matrix-vector products … and at most
n times as many additional operations"). The paper names no machine; this file fixes one.

**Formalization Note.**
* The core is the published real RAM `SmaleNinth.RAMInstr`: real registers, integer pointer
  registers, a real memory `ℤ → ℝ` addressed through pointers; `+ − × /` on reals (division by
  `0` returns `0`), arbitrary real constants, indirect load/store, pointer set/copy/increment/
  decrement, the branches `r ≤ 0` and `p ≤ p'`.
* Added instructions, each one step: `sqrt` (`Real.sqrt`, `0` on negatives), `tanh`, `draw`
  (the next point of a uniform draw tape on `[0,1]`), `idx` (an exact-integer real to a pointer;
  on a non-integer the machine is stuck forever, so no bits of a non-integer real can be
  extracted), `ofPtr` (a pointer to a real), `matvec` (one call of the matrix-vector oracle of
  the run), and `halt`.
* There is **no** floor, no rounding of non-integers, no `exp`, `log` or power instruction.
* The core's `accept`/`reject` leave the configuration unchanged, so a program that reaches one
  never halts; a program stops only through `halt` (or by running off its end).
* A run is parametrised by an oracle `O = ⟨m, f⟩` with `f : ℝ^m → ℝ^m`; `matvec src dst` reads
  `x_i = mem[p[src] + i]` (`i < m`) and writes `f(x)_i` to `mem[p[dst] + i]`. The number of
  oracle calls is counted separately (`State.calls`). `NoOracle P` says `P` has no `matvec`.
* Input: a list of reals in memory cells `0, 1, …`. Output: the memory block of length `p[1]`
  starting at address `p[2]` in the first halted state (`finalOut`).
-/

/-- An instruction of the randomized real RAM. -/
inductive Instr : Type
  /-- An instruction of the published core `SmaleNinth.RAMInstr`. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] := √(r[src])` (`Real.sqrt`, which is `0` on negative reals). -/
  | sqrt (dst src : ℕ)
  /-- `r[dst] := tanh (r[src])`. -/
  | tanh (dst src : ℕ)
  /-- `r[dst] :=` the next point of the uniform draw tape. -/
  | draw (dst : ℕ)
  /-- `p[q] := r[src]` if `r[src]` is an integer; on a non-integer the machine is stuck. -/
  | idx (q src : ℕ)
  /-- `r[dst] := p[q]`. -/
  | ofPtr (dst q : ℕ)
  /-- One call of the matrix-vector oracle: `mem[p[dst] + i] := f(x)_i` with
  `x_i = mem[p[src] + i]`, `i < m`. -/
  | matvec (src dst : ℕ)
  /-- Stop. -/
  | halt

/-- A program: one finite list of instructions, fixed before the input. -/
abbrev Program := List Instr

/-- `P` makes no oracle call. -/
def NoOracle (P : Program) : Prop := ∀ src dst, Instr.matvec src dst ∉ P

/-- A matrix-vector oracle on `ℝ^m`. -/
abbrev Oracle := Σ m : ℕ, ((Fin m → ℝ) → (Fin m → ℝ))

/-- The trivial oracle, used for programs that make no oracle call. -/
def noOracle : Oracle := ⟨0, fun x => x⟩

/-- The oracle `x ↦ A x` of a square matrix `A`. -/
def matOracle {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Oracle := ⟨n, fun x => A.mulVec x⟩

/-- A machine state: core configuration, number of draws used, number of oracle calls made,
and the halting flag. -/
structure State where
  /-- Program counter, real registers, pointer registers and memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- Number of uniform draws consumed. -/
  draws : ℕ
  /-- Number of oracle calls made. -/
  calls : ℕ
  /-- Whether the machine has halted. -/
  halted : Bool

/-- The draw tape: a sequence of points of `[0, 1]`. -/
abbrev Tape := ℕ → unitInterval

/-- The probability on draw tapes: the product of uniform (Lebesgue) measures on `[0, 1]`. -/
noncomputable def tapeMeasure : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

/-- The core instruction of an instruction (`accept` for the extensions; only used at positions
holding a core instruction). -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- Advance the program counter after updating the real registers. -/
def State.setReg (S : State) (regs : ℕ → ℝ) : State :=
  { S with cfg := { S.cfg with pc := S.cfg.pc + 1, regs := regs } }

/-- The memory after one oracle call: cells `base + i`, `i < m`, receive `y i`. -/
def writeBlock (mem : ℤ → ℝ) (base : ℤ) (m : ℕ) (y : Fin m → ℝ) : ℤ → ℝ := fun a =>
  if h : 0 ≤ a - base ∧ (a - base).toNat < m then y ⟨(a - base).toNat, h.2⟩ else mem a

/-- One step of `P` with oracle `O` on tape `ω`. Every executed instruction is one step. A halted
state is fixed, and running off the end of the program halts. -/
noncomputable def step (P : Program) (O : Oracle) (ω : Tape) (S : State) : State :=
  if S.halted then S else
  let r := S.cfg.regs
  match P[S.cfg.pc]? with
  | none => { S with halted := true }
  | some (.core _) => { S with cfg := SmaleNinth.RAMStep (P.map Instr.coreOf) S.cfg }
  | some (.sqrt dst src) => S.setReg (Function.update r dst (Real.sqrt (r src)))
  | some (.tanh dst src) => S.setReg (Function.update r dst (Real.tanh (r src)))
  | some (.draw dst) =>
      { S.setReg (Function.update r dst (ω S.draws : ℝ)) with draws := S.draws + 1 }
  | some (.idx q src) =>
      if ((⌊r src⌋ : ℤ) : ℝ) = r src then
        { S with cfg := ⟨S.cfg.pc + 1, r, Function.update S.cfg.ptrs q ⌊r src⌋, S.cfg.mem⟩ }
      else S
  | some (.ofPtr dst q) => S.setReg (Function.update r dst (S.cfg.ptrs q : ℝ))
  | some (.matvec src dst) =>
      { S with
        cfg := ⟨S.cfg.pc + 1, r, S.cfg.ptrs,
          writeBlock S.cfg.mem (S.cfg.ptrs dst) O.1
            (O.2 fun i => S.cfg.mem (S.cfg.ptrs src + (i : ℤ)))⟩
        calls := S.calls + 1 }
  | some .halt => { S with halted := true }

/-- The input memory holding the list `l` in cells `0, 1, …` and `0` elsewhere. -/
noncomputable def inputMem (l : List ℝ) : ℤ → ℝ := fun j => if 0 ≤ j then l.getD j.toNat 0 else 0

/-- The state after `t` steps of `P` with oracle `O` on input `l` and tape `ω` (program counter
`0`, all registers `0`, no draws, no calls). -/
noncomputable def run (P : Program) (O : Oracle) (l : List ℝ) (ω : Tape) (t : ℕ) : State :=
  (step P O ω)^[t] ⟨⟨0, fun _ => 0, fun _ => 0, inputMem l⟩, 0, 0, false⟩

/-- The output of a state: the memory block of length `p[1]` starting at address `p[2]`. -/
noncomputable def output (S : State) : List ℝ :=
  (List.range (S.cfg.ptrs 1).toNat).map fun j => S.cfg.mem (S.cfg.ptrs 2 + (j : ℤ))

/-- Every execution of `P` with oracle `O` on input `l` halts within `B` steps: on every tape
the state after `⌊B⌋₊` steps is halted. -/
def HaltsWithin (P : Program) (O : Oracle) (l : List ℝ) (B : ℝ) : Prop :=
  ∀ ω : Tape, (run P O l ω ⌊B⌋₊).halted = true

open Classical in
/-- The output of the run of `P` with oracle `O` on input `l` and tape `ω`, read in the first
halted state (the empty list if the run never halts). -/
noncomputable def finalOut (P : Program) (O : Oracle) (l : List ℝ) (ω : Tape) : List ℝ :=
  if h : ∃ t, (run P O l ω t).halted = true then output (run P O l ω (Nat.find h)) else []

/-- On tape `ω`, the run of `P` with oracle `O` on input `l` halts after at most `A` oracle calls
and at most `B` other steps, and its output satisfies `good`. -/
def HaltsWithCounts (P : Program) (O : Oracle) (l : List ℝ) (ω : Tape) (A B : ℝ)
    (good : List ℝ → Prop) : Prop :=
  ∃ t : ℕ, (run P O l ω t).halted = true ∧ ((run P O l ω t).calls : ℝ) ≤ A ∧
    (t : ℝ) - ((run P O l ω t).calls : ℝ) ≤ B ∧ good (output (run P O l ω t))

end OptRobustCD


