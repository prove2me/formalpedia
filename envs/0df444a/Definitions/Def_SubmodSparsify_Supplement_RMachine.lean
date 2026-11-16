-- Prove2me | Definitions.Def_SubmodSparsify_Supplement_RMachine
-- name    : SubmodSparsify_Supplement_RMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:10:30.477213+00:00
-- url     : https://prove2.me/theorems/0f010b7f-d50e-4760-bcda-df7769481fbd
-- title:
--   The randomized $m$-oracle RAM with a real input cell
-- statement:
--   The machine on which the randomized score computation of Theorem A.1 runs. It is the base mission's deterministic exact-arithmetic RAM with $m$ value oracles $f_0,\dots,f_{m-1}$ (`SubmodSparsify.Machine`), extended by one instruction: a **fair coin**, which writes the next bit of a random tape $\omega \in \{0,1\}^{\mathbb N}$ to a register and advances the tape cursor, as in the published value-oracle RAM `FasterSFM.Machine`. The integer input list is placed in integer memory and the real failure parameter $\delta$ in real-memory cell $-1$; outputs are read from real memory. Every executed instruction, including a value query and a coin, costs one unit of work (unit-cost oracle), and halted states stutter at no cost. Admissible programs use rational literals only.
--
--   This gives the paper's "for fixed $\beta$, one can compute in polynomial time" (Theorem A.1, Lemma A.3) a precise meaning: a single program whose running time on every coin tape is bounded by a polynomial in $n$, $m$ and $\log(1/\delta)$.
--
--   **Formalization Note** The tape law is the published `FasterSFM.coinTape` (independent fair bits). Base instructions are executed by the base `step` on the program with each coin replaced by a placeholder, which keeps all jump targets.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6793d37e5008919a4795e2e18da7fa5049f06ad4d1b929ac6d7fbc634), Theorem A.1, p.43; Lemma A.3, p.44; §A.4, pp.53–55

import Mathlib
import Definitions.Def_SubmodSparsify_Machine
import Definitions.Def_FasterSFM_Machine

namespace SubmodSparsify.Supplement

/-!
# The randomized `m`-oracle RAM with a real input cell (Theorem A.1, "polynomial time")

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Theorem A.1, p.43 ("for fixed β, one
can compute in polynomial time positive scores p̃₁, …, p̃_m […] such that, with probability at
least 1−δ/4, p̃ᵢ ≥ pᵢ for every i"); Lemma A.3, p.44 ("in time polynomial in n, m, and
log(1/δ′)"); §A.4, pp.53–55 (the scores are estimated by sampling).

The machine is the published deterministic `m`-oracle RAM `SubmodSparsify.Machine` of the base
mission with one extra instruction, the fair coin of the published `FasterSFM.Machine`
(`r[d] := 1` if the next tape bit is `true`, else `0`; the tape cursor advances), and with the
failure parameter `δ` placed in a real-memory input cell.

**Formalization Note.**
* `base i` executes the base instruction `i` exactly as `SubmodSparsify.step` does (on the
  program obtained by replacing every `coin` by a placeholder, which keeps every jump target);
  `coin d` costs one unit of `work`, writes the next tape bit to register `d` and advances the
  cursor. Halted states stutter at no cost.
* Input: the integer list `input` in integer-memory cells `0, 1, …` (Theorem A.1: `[n, m]`), and
  the real `δ` in real-memory cell `−1`; every other cell, register, pointer and bitmap starts at
  `0`/`∅`. The output is read from real memory (cell `i` holds the `i`-th value).
* The tape `ω : ℕ → Bool` is drawn from the published fair-coin law `FasterSFM.coinTape`.
* Every executed instruction costs one unit of `work`, a value query included (unit-cost
  oracle, as in Lemma A.3's "time polynomial in n, m, and log(1/δ′)").
* Admissible programs use rational literals only and no core `accept`/`reject`.
-/

/-- An instruction of the randomized machine: a base instruction, or a fair coin. -/
inductive RInstr where
  | base (instruction : SubmodSparsify.Instr)
  | coin (dst : ℕ)

/-- A randomized program: one finite list of instructions, the same for every input. -/
abbrev RProgram := List RInstr

/-- The base program in which every `coin` is replaced by a placeholder (positions, hence jump
targets, are unchanged). -/
def RProgram.toBase (P : RProgram) : SubmodSparsify.Program :=
  P.map fun op => match op with
    | .base i => i
    | .coin _ => .core (.const 0 0)

/-- Admissibility: every real literal is rational and the core halting instructions
`accept`/`reject` do not occur. -/
def RAdmissible (P : RProgram) : Prop :=
  ∀ op ∈ P, match op with
    | .base (.core (.const _ value)) => ∃ q : ℚ, value = (q : ℝ)
    | .base (.core .accept) | .base (.core .reject) => False
    | _ => True

/-- A state of the randomized machine: a base state and the coin-tape cursor. -/
structure RState (n : ℕ) where
  base : SubmodSparsify.State n
  cursor : ℕ

/-- The initial state on integer input `input` and real input `δ` (real-memory cell `−1`). -/
def rinit (n : ℕ) (input : List ℤ) (δ : ℝ) : RState n :=
  let s := SubmodSparsify.init n input
  ⟨{ s with core := { s.core with mem := fun j => if j = -1 then δ else 0 } }, 0⟩

/-- One step of `P` with value oracles `f` and coin tape `ω`. -/
noncomputable def rstep {n m : ℕ} (P : RProgram) (f : Fin m → Finset (Fin n) → ℝ)
    (ω : ℕ → Bool) (s : RState n) : RState n :=
  if s.base.halted then s else
    match P[s.base.core.pc]? with
    | some (.coin d) =>
        ⟨{ s.base with
            work := s.base.work + 1
            core := { s.base.core with
              pc := s.base.core.pc + 1
              regs := Function.update s.base.core.regs d (if ω s.cursor then 1 else 0) } },
          s.cursor + 1⟩
    | _ => ⟨SubmodSparsify.step P.toBase f s.base, s.cursor⟩

/-- The state after `t` steps of `P` on oracles `f`, integer input `input`, real input `δ` and
coin tape `ω`. -/
noncomputable def rrun {n m : ℕ} (P : RProgram) (f : Fin m → Finset (Fin n) → ℝ)
    (input : List ℤ) (δ : ℝ) (ω : ℕ → Bool) (t : ℕ) : RState n :=
  (rstep P f ω)^[t] (rinit n input δ)

end SubmodSparsify.Supplement


