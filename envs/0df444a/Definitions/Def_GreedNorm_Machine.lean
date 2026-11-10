-- Prove2me | Definitions.Def_GreedNorm_Machine
-- name    : GreedNorm_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:49.107386+00:00
-- url     : https://prove2.me/theorems/ac3c6b1f-4ef5-420c-bf1a-7a2b5de481ca
-- title:
--   Deterministic value-oracle real RAM for GLB
-- statement:
--   The machine model in which the algorithms of the mission are stated. It is a real RAM with unit cost per instruction: real registers, integer pointer registers, a real memory indexed by $\mathbb Z$ and an integer memory indexed by $\mathbb Z$. Instructions are those of the published real pointer machine `SmaleNinth.RAMInstr` (rational constants, $+,-,\times,\div$ with $x/0=0$, indirect loads and stores, pointer updates, the tests $r\le 0$ and $p\le p'$), integer pointer arithmetic $+,-,\times$, integer loads and stores, the cast of a pointer to a real, `halt`, and two **oracle instructions**:
--
--   1. `innerQuery d i b` writes $f_{p[i]}\bigl(\mathrm{mem}[p[b]],\dots,\mathrm{mem}[p[b]+n-1]\bigr)$ into register $d$ (or $0$ when $p[i]\notin[0,m)$);
--   2. `outerQuery d b` writes $g\bigl(\mathrm{mem}[p[b]],\dots,\mathrm{mem}[p[b]+m-1]\bigr)$ into register $d$.
--
--   Each oracle call costs one step. A program is one finite list of instructions; it is **admissible** if its real literals are rational and it does not use the core's `accept`/`reject`. The run is deterministic; the time of a run is the number of steps until `halt`.
--
--   The norms of GLB have no finite description, so value-oracle access is the input model in which "polynomial time" is meaningful for this problem.
--
--   **Formalization Note** The core is the public `SmaleNinth` real RAM; the extension follows the public `FasterSFM.Machine` and `LSWNewArcAudit.NewArc` oracle RAMs, without coin tape, square root or bitmaps. There is no exp, log, floor, real-to-integer cast or sort instruction. A program counter outside the program is stuck (the run never halts); a halted state stays halted.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 1.3, p.2 (PDF 4); Lemma 3.14, p.9 (PDF 11)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace GreedNorm

/-!
# The deterministic value-oracle real RAM for Generalized Load Balancing

Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), Theorem 1.3, p.2 (PDF 4): "GLB admits a deterministic approximation", and
Lemma 3.14, p.9 (PDF 11): "There is an exact algorithm for NormBudgCard". The norms `f_i`, `g`
of Definition 1.1, p.1 (PDF 3), have no finite description, so the algorithms access them as value
oracles.

**Formalization Note.**
* The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (constants,
  `+ − × ÷` with `x / 0 = 0`, indirect real load/store through pointer registers, pointer
  set/copy/increment/decrement, the jumps `r ≤ 0` and `p ≤ p'`). The extensions follow the
  published `FasterSFM.Machine` / `LSWNewArcAudit.NewArc` oracle RAMs (integer pointer arithmetic,
  integer memory `ℤ → ℤ`, pointer-to-real cast), but the machine is deterministic (no coin tape),
  has no square root and no bitmaps, and its two oracle instructions query the norms of GLB on
  a block of real memory:
  - `innerQuery d i b`: `r[d] := f_{p[i]} (j ↦ mem (p[b] + j))` for `j : Fin n`, when
    `0 ≤ p[i] < m`; otherwise `r[d] := 0`;
  - `outerQuery d b`: `r[d] := g (i ↦ mem (p[b] + i))` for `i : Fin m`.
* There is no exp, log, floor, real-to-integer cast, sort or argmin instruction. Unit cost: every
  executed instruction, an oracle call included, is one step; the time of a run is the index `t`
  of the first halted state. A program counter outside the program is stuck (never halts).
  After `halt` the state stutters.
* Admissible programs use rational real literals only and no core `accept`/`reject` (output is
  through `halt` and integer memory). The program is one finite list, the same for every input.
* `f` and `g` enter `step` only in the two query branches.
-/

namespace Machine

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor
carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd/Sub/Mul d a b`: `p[d] := p[a] ∘ p[b]` on integer pointers.
* `integerLoad d a` / `integerStore a b`: `p[d] := I[p[a]]` / `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `innerQuery d i b`: `r[d] := f_{p[i]}(mem[p[b] .. p[b] + n − 1])` (or `0` if `p[i] ∉ [0, m)`).
* `outerQuery d b`: `r[d] := g(mem[p[b] .. p[b] + m − 1])`.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | pointerMul (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | innerQuery (dst machine base : ℕ)
  | outerQuery (dst base : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- Admissibility: every real literal is rational, and the core halting instructions
`accept`/`reject` do not occur. This restricts the existentially chosen program, never the
input. -/
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

/-- A machine state: the core configuration (program counter, real registers, pointer registers,
real memory), the integer memory, and the halting flag. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  halted : Bool

/-- The initial state on a given input: program counter `0`, all real and pointer registers `0`,
real memory `realMemory`, integer memory `integerMemory`, not halted. -/
def init (realMemory : ℤ → ℝ) (integerMemory : ℤ → ℤ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, realMemory⟩, integerMemory, false⟩

/-- One step of program `P` with inner oracles `f : Fin m → (Fin n → ℝ) → ℝ` and outer oracle
`g : (Fin m → ℝ) → ℝ`. A halted state stutters; `f` and `g` occur only in the query branches. -/
noncomputable def step {n m : ℕ} (P : Program) (f : Fin m → (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (s : State) : State :=
  if s.halted then s else
    let t : State := { s with core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => s
    | some (.core _) => { s with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.pointerMul d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a * s.core.ptrs b) } }
    | some (.integerLoad d a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory :=
            Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.innerQuery d i b) =>
        let value : ℝ :=
          if hi : 0 ≤ s.core.ptrs i ∧ (s.core.ptrs i).toNat < m then
            f ⟨(s.core.ptrs i).toNat, hi.2⟩ (fun j : Fin n => s.core.mem (s.core.ptrs b + (j : ℤ)))
          else 0
        { t with core := { t.core with regs := Function.update s.core.regs d value } }
    | some (.outerQuery d b) =>
        let value : ℝ := g (fun i : Fin m => s.core.mem (s.core.ptrs b + (i : ℤ)))
        { t with core := { t.core with regs := Function.update s.core.regs d value } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀` with oracles `f`, `g`. -/
noncomputable def run {n m : ℕ} (P : Program) (f : Fin m → (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (s₀ : State) (t : ℕ) : State :=
  (step P f g)^[t] s₀

end Machine

end GreedNorm


