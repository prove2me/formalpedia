-- Prove2me | Definitions.Def_LinfContractionFP_Machine
-- name    : LinfContractionFP_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:10.482283+00:00
-- url     : https://prove2.me/theorems/75e68f39-5d67-49c2-8a32-219f0c536820
-- title:
--   The unit-cost real RAM with an oracle for $f$: instructions, one step, runs, input and output layout
-- statement:
--   The machine on which the running time of Theorem 1 is measured: the published unit-cost real RAM (real registers, integer pointer registers, a real memory $\mathbb Z\to\mathbb R$ addressed through pointers; the operations $+,-,\times,/$ on reals, real constants, indirect load and store, pointer set, copy, increment and decrement, the branches "$r\le 0$" and "$p\le p'$", `accept` and `reject`), extended by **one** instruction that evaluates $f:\mathbb R^d\to\mathbb R^d$.
--
--   The instruction `query src dst` reads the $d$ reals $x_i=\mathrm{mem}[p_{\mathrm{src}}+i]$, $0\le i<d$, and writes $f(x)_i$ to $\mathrm{mem}[p_{\mathrm{dst}}+i]$. Every executed instruction, the query included, costs one step.
--
--   A run of a program $P$ starts with program counter $0$, all registers $0$, and memory $\mathrm{mem}[0]=d$, $\mathrm{mem}[1]=\gamma$, $\mathrm{mem}[2]=\varepsilon$, all other cells $0$. It halts when the program counter reaches an `accept` instruction; the output is then the vector $x_i=\mathrm{mem}[3+i]$, $0\le i<d$.
--
--   This file fixes the "unit-cost real machine" of footnote 6 (p.19) in which the paper counts arithmetic operations, comparisons and exact evaluations of $f$.
--
--   **Formalization Note** There is no floor, no real-to-integer conversion, no square root, logarithm or exponential, no sort or median instruction, and no coin, so programs are deterministic. $f$ is total; on a point outside $[0,1]^d$ the query returns whatever $f$ returns there, so a program must clip before querying. `reject` and an invalid program counter never halt. Division by zero returns $0$.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), footnote 6, p.19; proof of Theorem 1, p.21

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace LinfContractionFP

/-!
# The unit-cost real RAM with an oracle for `f`

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), footnote 6, p.19 ("we analyze the complexity assuming a unit-cost
real machine") and the proof of Theorem 1, p.21 ("the total number of arithmetic operations,
comparisons, and exact evaluations of f performed by Solve(f, ε)").

**Formalization Note.**
* The core is the published real RAM `SmaleNinth.RAMInstr` (real registers, real memory
  `ℤ → ℝ` addressed through integer pointer registers; `+ − × /` on reals, real constants,
  indirect load and store, pointer set/copy/increment/decrement, the branches `r ≤ 0` and
  `p ≤ p'`, `accept`, `reject`). It has no floor, no real-to-integer conversion, no square root,
  logarithm or exponential, no sorting or median instruction, and no coins.
* One instruction is added: `query src dst` reads the `d` reals `x_i = mem[p[src] + i]`
  (`0 ≤ i < d`), evaluates `f` once, and writes `(f x)_i` to `mem[p[dst] + i]`. It is the only
  access to `f` and is exact (the paper's "exact evaluations of f"). `f` is total: on a point
  outside `[0,1]^d` it returns whatever the given `f` returns, so a program that wants the
  clipped extension must clip first.
* Cost: every executed instruction, the query included, is one step. The semantics is
  parametrised by `d` and `f`, which appear only in the query branch.
* A run starts at `pc = 0` with all registers `0` and the input memory `inputMem d γ ε`
  (`mem[0] = d`, `mem[1] = γ`, `mem[2] = ε`, all other cells `0`). It halts when the program
  counter reaches an `accept` instruction (the core leaves such a configuration unchanged);
  `reject` and an invalid program counter never halt. The output of a halted configuration is
  the vector `x_i = mem[3 + i]`, `0 ≤ i < d`.
-/

/-- An instruction: a core real-RAM instruction, or one evaluation of `f`. -/
inductive Instr : Type
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `mem[p[dst] + i] := f(x)_i` for `0 ≤ i < d`, where `x_i = mem[p[src] + i]`. -/
  | query (src dst : ℕ)

/-- A program: one finite list of instructions, fixed before the input. -/
abbrev Program := List Instr

/-- The core table of `P`; a `query` is a placeholder that `step` always dispatches itself. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | .query _ _ => .const 0 0

/-- One step of `P` in dimension `d` with oracle `f`. -/
noncomputable def step (d : ℕ) (f : (Fin d → ℝ) → (Fin d → ℝ)) (P : Program)
    (s : SmaleNinth.RAMConfig) : SmaleNinth.RAMConfig :=
  match P[s.pc]? with
  | some (.query src dst) =>
      let y := f fun i : Fin d => s.mem (s.ptrs src + (i : ℤ))
      { s with
        pc := s.pc + 1
        mem := fun a =>
          if h : 0 ≤ a - s.ptrs dst ∧ a - s.ptrs dst < (d : ℤ) then
            y ⟨(a - s.ptrs dst).toNat, by omega⟩
          else s.mem a }
  | _ => SmaleNinth.RAMStep (coreProgram P) s

/-- The input memory: `mem[0] = d`, `mem[1] = γ`, `mem[2] = ε`, every other cell `0`. -/
noncomputable def inputMem (d : ℕ) (γ ε : ℝ) : ℤ → ℝ := fun a =>
  if a = 0 then (d : ℝ) else if a = 1 then γ else if a = 2 then ε else 0

/-- The configuration after `t` steps of `P` on input `(d, γ, ε)` with oracle `f`. -/
noncomputable def run (P : Program) (d : ℕ) (f : (Fin d → ℝ) → (Fin d → ℝ)) (γ ε : ℝ)
    (t : ℕ) : SmaleNinth.RAMConfig :=
  (step d f P)^[t] ⟨0, fun _ => 0, fun _ => 0, inputMem d γ ε⟩

/-- The configuration `s` is halted: its program counter carries `accept`. -/
def Halted (P : Program) (s : SmaleNinth.RAMConfig) : Prop :=
  P[s.pc]? = some (.core .accept)

/-- The output vector of a configuration: `x_i = mem[3 + i]` for `0 ≤ i < d`. -/
def output (d : ℕ) (s : SmaleNinth.RAMConfig) : Fin d → ℝ := fun i => s.mem (3 + (i : ℤ))

end LinfContractionFP


