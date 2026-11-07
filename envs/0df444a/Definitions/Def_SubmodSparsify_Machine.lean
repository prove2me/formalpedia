-- Prove2me | Definitions.Def_SubmodSparsify_Machine
-- name    : SubmodSparsify_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:45.322764+00:00
-- url     : https://prove2.me/theorems/20f026ac-37c4-4c65-bcad-9bfa801d16aa
-- title:
--   Deterministic exact-arithmetic RAM with $m$ value oracles and per-query cost $T_{\mathrm{eval}}$
-- statement:
--   The machine on which Algorithm 1 runs: a **real RAM** with exact arithmetic ($+, -, \times, \div, \sqrt{\cdot}$ on reals, integer pointers and memory, one-bit bitmaps encoding subsets of $[n]$) and **$m$ value oracles** $f_1, \dots, f_m : 2^{[n]} \to \mathbb R$. The instruction `query d o b` writes $f_{p[o]}(\text{bitmap } p[b])$ into a real register; it is the only access to the $f_i$. A program is one finite list of instructions used for every $n$, $m$ and input; it has no coin, so its runs are deterministic. The input (a list of integers) is placed in integer memory, the output is read from real memory after `halt`.
--
--   Every executed instruction costs one unit of work, and the **running time** with oracle cost $T_{\mathrm{eval}}$ charges each query $T_{\mathrm{eval}}$ and every other instruction $1$:
--
--   $$\mathrm{time}(s) = (\mathrm{work}(s) - \mathrm{queries}(s)) + T_{\mathrm{eval}} \cdot \mathrm{queries}(s).$$
--
--   This is the time model of Theorem 4.1 and Claim 4.3 ("let $T_{\mathrm{eval}}$ denote the time of a single value-oracle query to $f_i$").
--
--   **Formalization Note** The machine extends the published value-oracle RAM `FasterSFM.Machine` (same scalar core `SmaleNinth.RAMInstr`, pointer arithmetic, integer memory, $\sqrt{\cdot}$ with $\sqrt{x} = 0$ for $x < 0$, $x/0 = 0$, bitmaps) with $m$ oracles instead of one and real-memory output, and drops the coin. A query with an oracle index outside $[0, m)$ returns $0$. Admissible programs use rational literals only. After `halt` the state does not change.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), p.3 (PDF p.5); Theorem 4.1, p.18 (PDF p.20); Claim 4.3, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace SubmodSparsify

/-!
# The deterministic exact-arithmetic RAM with m value oracles (Theorem 4.1, Claim 4.3)

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), p.3 ("let Teval denote the time of
a single value-oracle query to fi"), Theorem 4.1, p.18 ("deterministically computes […] in
time O(mn³Tmin(n)²(Teval + n))"), Claim 4.3, p.22.

The machine on which Algorithm 1 runs. It is the published value-oracle RAM
`FasterSFM.Machine` (the scalar core `SmaleNinth.RAMInstr`, integer pointer arithmetic,
integer memory, `√`, one-bit bitmaps), without the coin, with `m` value oracles
`f₀, …, f_{m−1} : Finset (Fin n) → ℝ` instead of one, and with real-memory output.

**Formalization Note.**
* Ground set `Fin n`. The input is a list of integers placed in integer memory cells
  `0, 1, …` (Theorem 4.1: `[n, m]`; Claim 4.3: `[n, m, u, dir]`); every other cell, register,
  pointer, real-memory cell and bitmap starts at `0`/`∅`. The oracles are reachable only through
  `query`.
* `query dst oracle bank`: `r[dst] := f_{p[oracle]}(bitmap p[bank])` when
  `0 ≤ p[oracle] < m`, else `0`; every executed `query` adds one to `queries`.
* `halt` stops the machine; the output is read from real memory (`mem i` holds the `i`-th
  output value). After `halt` the state stutters with no further cost.
* There is no coin: the machine is deterministic.
* Every executed instruction costs one unit of `work`, a `query` included. The running time
  with oracle cost `Teval` charges each query `Teval` and every other instruction `1`:
  `charged s Teval = (work − queries) + Teval · queries`.
* Admissible programs use rational literals only and no core `accept`/`reject`.
-/

/-- An instruction of the `m`-oracle RAM. Register, pointer and label arguments are natural
numbers; no constructor carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd/Sub/Mul d a b`: `p[d] := p[a] ∘ p[b]` on integer pointers.
* `integerLoad d a` / `integerStore a b`: `p[d] := I[p[a]]` / `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `sqrt d a`: `r[d] := √(r[a])`.
* `bitWrite bank elt val`: set bit `p[elt]` of bitmap `p[bank]` to `r[val] ≠ 0`.
* `bitRead d bank elt`: `r[d] := 1` if bit `p[elt]` of bitmap `p[bank]` is set, else `0`.
* `query d oracle bank`: `r[d] := f_{p[oracle]}(bitmap p[bank])`.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | pointerMul (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | bitWrite (bank element value : ℕ)
  | bitRead (dst bank element : ℕ)
  | query (dst oracle bank : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every `n`, `m` and every input. -/
abbrev Program := List Instr

/-- Admissibility: every real literal is rational and the core halting instructions
`accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, dispatched by
`step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state for ground set `Fin n`. -/
structure State (n : ℕ) where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  bitmap : ℤ → Finset (Fin n)
  halted : Bool
  queries : ℕ
  work : ℕ

/-- The initial state on input `input` (integer memory cells `0, 1, …`). -/
def init (n : ℕ) (input : List ℤ) : State n :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun i => if 0 ≤ i then input.getD i.toNat 0 else 0, fun _ => ∅, false, 0, 0⟩

/-- One step of `P` with value oracles `f`. Halted states stutter at no cost; every other step
costs one unit of work. `f` occurs only in the `query` branch. Bit indices outside `[0, n)` read
`0` and write nothing. -/
noncomputable def step {n m : ℕ} (P : Program) (f : Fin m → Finset (Fin n) → ℝ)
    (s : State n) : State n := by
  classical
  exact if s.halted then s else
    let t := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) =>
        { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
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
        { t with integerMemory := Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.sqrt d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.sqrt (s.core.regs a)) } }
    | some (.bitWrite b e v) =>
        if hb : 0 ≤ s.core.ptrs e ∧ (s.core.ptrs e).toNat < n then
          let j : Fin n := ⟨(s.core.ptrs e).toNat, hb.2⟩
          let bank := s.core.ptrs b
          let contents := if s.core.regs v = 0 then (s.bitmap bank).erase j
            else insert j (s.bitmap bank)
          { t with bitmap := Function.update s.bitmap bank contents }
        else t
    | some (.bitRead d b e) =>
        let value : ℝ := if hb : 0 ≤ s.core.ptrs e ∧ (s.core.ptrs e).toNat < n then
          if (⟨(s.core.ptrs e).toNat, hb.2⟩ : Fin n) ∈ s.bitmap (s.core.ptrs b) then 1 else 0
          else 0
        { t with core := { t.core with regs := Function.update s.core.regs d value } }
    | some (.query d o b) =>
        let value : ℝ := if ho : 0 ≤ s.core.ptrs o ∧ (s.core.ptrs o).toNat < m then
          f ⟨(s.core.ptrs o).toNat, ho.2⟩ (s.bitmap (s.core.ptrs b)) else 0
        { t with
          queries := s.queries + 1
          core := { t.core with regs := Function.update s.core.regs d value } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` on oracles `f` and input `input`. -/
noncomputable def run {n m : ℕ} (P : Program) (f : Fin m → Finset (Fin n) → ℝ)
    (input : List ℤ) (t : ℕ) : State n :=
  (step P f)^[t] (init n input)

/-- The running time of a state when each value-oracle query costs `Teval` and every other
executed instruction costs `1`. -/
def charged {n : ℕ} (s : State n) (Teval : ℝ) : ℝ :=
  ((s.work : ℝ) - (s.queries : ℝ)) + Teval * (s.queries : ℝ)

end SubmodSparsify


