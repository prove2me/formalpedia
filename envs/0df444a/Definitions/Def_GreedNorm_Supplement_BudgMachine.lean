-- Prove2me | Definitions.Def_GreedNorm_Supplement_BudgMachine
-- name    : GreedNorm_Supplement_BudgMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:51:47.106215+00:00
-- url     : https://prove2.me/theorems/4d7e3edb-5647-4bcf-8f91-15853aece456
-- title:
--   Deterministic BudgCard-oracle real RAM for Nested Cost Allocation
-- statement:
--   The machine model of Theorem 3.2. It is the base mission's deterministic real RAM (real and integer pointer registers, real and integer memory indexed by $\mathbb Z$, the real-RAM arithmetic and jumps, integer pointer arithmetic, unit cost per instruction), with its two GLB oracle instructions replaced by three oracle instructions for Nested Cost Allocation over the universe $U=\{0,\dots,n-1\}$ with $m$ parts. A subset of $U$ is held as an integer block, $e\in S$ iff the cell at base$+e$ is nonzero.
--
--   1. `loadQuery`: write $\mathrm{load}_i(S)$ into a real register, for the part $i$ named by a pointer register and the set $S$ held at a given block.
--   2. `outerQuery`: write $g(v)$ for the vector $v\in\mathbb R^m$ held in a real-memory block.
--   3. `budgQuery`: ask the BudgCard algorithm the instance with universe $U'$ (a block), load function $\mathrm{load}_i$ and budget $B$ (a real register), and write the indicator of its answer into another block.
--
--   Every executed instruction, oracle calls included, costs one step. Programs are finite lists fixed before the input, admissible programs use only rational literals, and the loads, $g$ and the BudgCard algorithm are reachable only through these instructions. This models "an $\alpha$-approximation algorithm for BudgCard implies an approximation algorithm for SubaddNestedCostAlloc" as an oracle reduction.
--
--   **Formalization Note** States and initial states are the base machine's. An out-of-range part index makes `loadQuery` return $0$ and `budgQuery` do nothing.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 3.2 and Definition 3.1, p.6 (PDF 8); Definition 1.2, p.2 (PDF 4)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_GreedNorm_Machine

namespace GreedNorm

/-!
# The deterministic BudgCard-oracle real RAM for Nested Cost Allocation

Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), Theorem 3.2, p.6 (PDF 8): "An α-approximation algorithm for BudgCard implies a
(3(1+ϵ)/α · ln n)-approximation algorithm for SubaddNestedCostAlloc". The load functions
`load_i : 2^U → ℝ_{≥0}` and the norm `g` of Definition 1.2, p.2 (PDF 4), have no finite
description, and the BudgCard algorithm is arbitrary, so all three are oracles.

**Formalization Note.**
* The machine is the published `GreedNorm.Machine` (same `SmaleNinth` real-RAM core, integer
  pointer arithmetic, integer memory, pointer-to-real cast, unit cost, deterministic, states
  `GreedNorm.Machine.State` and initial states `GreedNorm.Machine.init`), with its two GLB oracle
  instructions replaced by three Nested Cost Allocation oracle instructions. The universe is
  `Fin n`; a set `S ⊆ Fin n` is held as an integer block: `e ∈ S` iff `I[base + e] ≠ 0`.
  - `loadQuery d i b`: `r[d] := load_{p[i]}({e | I[p[b] + e] ≠ 0})` when `0 ≤ p[i] < m`, else `0`;
  - `outerQuery d b`: `r[d] := g(i ↦ mem(p[b] + i))` for `i : Fin m`;
  - `budgQuery i b r c`: when `0 ≤ p[i] < m`, the BudgCard oracle is asked the instance
    (universe `U' = {e | I[p[b] + e] ≠ 0}`, load function `load_{p[i]}`, budget `r[r]`) and its
    answer `S` is written as `I[p[c] + e] := 1` if `e ∈ S`, `0` otherwise, for every `e : Fin n`
    (other cells unchanged); otherwise nothing changes but the program counter.
* Unit cost: every executed instruction, an oracle call included, is one step. A program counter
  outside the program is stuck; after `halt` the state stutters.
* Admissible programs use rational real literals only and no core `accept`/`reject`.
* `load`, `g` and `budg` enter `step` only in the three query branches.
-/

namespace Supplement.BudgMachine

/-- An instruction: the extension instructions of `GreedNorm.Machine` with the three Nested Cost
Allocation oracle instructions `loadQuery`, `outerQuery`, `budgQuery` (see the module doc). -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | pointerMul (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | loadQuery (dst machine base : ℕ)
  | outerQuery (dst base : ℕ)
  | budgQuery (machine universeBase budgetReg answerBase : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- Admissibility: every real literal is rational, and `accept`/`reject` do not occur. -/
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

/-- The set `{e : Fin n | I[base + e] ≠ 0}` held in integer memory at `base`. -/
def readSet {n : ℕ} (I : ℤ → ℤ) (base : ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun e : Fin n => I (base + (e : ℤ)) ≠ 0

/-- Integer memory `I` with the indicator of `S ⊆ Fin n` written at `base, …, base + n - 1`. -/
def writeSet {n : ℕ} (I : ℤ → ℤ) (base : ℤ) (S : Finset (Fin n)) : ℤ → ℤ :=
  fun a => if h : 0 ≤ a - base ∧ (a - base).toNat < n then
      (if (⟨(a - base).toNat, h.2⟩ : Fin n) ∈ S then 1 else 0)
    else I a

/-- One step of `P` with load oracles `load`, outer oracle `g` and BudgCard oracle `budg`
(`budg i U' B` is the oracle's answer on universe `U'`, load function `load i`, budget `B`). -/
noncomputable def step {n m : ℕ} (P : Program) (load : Fin m → Finset (Fin n) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (budg : Fin m → Finset (Fin n) → ℝ → Finset (Fin n))
    (s : Machine.State) : Machine.State :=
  if s.halted then s else
    let t : Machine.State := { s with core := { s.core with pc := s.core.pc + 1 } }
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
    | some (.loadQuery d i b) =>
        let value : ℝ :=
          if hi : 0 ≤ s.core.ptrs i ∧ (s.core.ptrs i).toNat < m then
            load ⟨(s.core.ptrs i).toNat, hi.2⟩ (readSet s.integerMemory (s.core.ptrs b))
          else 0
        { t with core := { t.core with regs := Function.update s.core.regs d value } }
    | some (.outerQuery d b) =>
        let value : ℝ := g (fun i : Fin m => s.core.mem (s.core.ptrs b + (i : ℤ)))
        { t with core := { t.core with regs := Function.update s.core.regs d value } }
    | some (.budgQuery i b r c) =>
        if hi : 0 ≤ s.core.ptrs i ∧ (s.core.ptrs i).toNat < m then
          let S := budg ⟨(s.core.ptrs i).toNat, hi.2⟩
            (readSet s.integerMemory (s.core.ptrs b)) (s.core.regs r)
          { t with integerMemory := writeSet s.integerMemory (s.core.ptrs c) S }
        else t
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀` with oracles `load`, `g`, `budg`. -/
noncomputable def run {n m : ℕ} (P : Program) (load : Fin m → Finset (Fin n) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (budg : Fin m → Finset (Fin n) → ℝ → Finset (Fin n))
    (s₀ : Machine.State) (t : ℕ) : Machine.State :=
  (step P load g budg)^[t] s₀

end Supplement.BudgMachine

end GreedNorm


