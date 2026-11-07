-- Prove2me | Definitions.Def_ShadowBootstrap_stateFrom
-- name    : ShadowBootstrap_stateFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:35.923229+00:00
-- url     : https://prove2.me/theorems/3d58f75a-4b97-4d10-840b-16cdd111d5f7
-- title:
--   Real-RAM runs: two-bank input, time, working memory, output, rational literals
-- statement:
--   The paper bounds classical post-processing "time" and "working memory" (Theorems 7.1, 7.3, Lemma 6.3) by counting arithmetic operations, including square roots (normalizations, $2\times2$ eigenvectors, trace distances). The model is the unit-cost **real RAM** with exact $+, -, \times, \div, \sqrt{\cdot}$ on real cells, integer index cells with $+$ and $-$, indirect loads and stores and comparisons (the published `MatMulTimeLP.RealRAM`).
--
--   1. **Input.** A two-bank initial state: integer data (the register size, circuit descriptions, shot counts) in the index cells and real data ($\epsilon$, $\delta$, histogram counts, real and imaginary parts of complex vectors) in the real cells.
--   2. **Time.** The number of executed instructions, including the final `halt`.
--   3. **Working memory.** The number of distinct cells, of either bank, written before the program halts.
--   4. **Output.** At the halting state, the amplitude of $z \in \{0,1\}^n$ is read from the real cells $2\,\mathrm{index}(z)$ and $2\,\mathrm{index}(z)+1$ after the input, with $\mathrm{index}(z) = \sum_j z_j 2^{n-1-j}$.
--   5. **Programs** use only rational real literals and no random instructions.
--
--   **Formalization Note** The two-bank input is needed because the machine has no real-to-index conversion. Overwritten input cells count as written. Rational literals prevent a real constant from encoding a table, and the absence of random instructions makes the post-processing deterministic, as in the paper.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Theorems 7.1 and 7.3, pp.27–28; Lemma 6.3, p.24; Lemma 6.1, p.23; §3.5, p.10

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear MatMulTimeLP

namespace ShadowBootstrap

/-- The all-zero random tape. The programs of this mission contain no `gauss`/`unif`
(`NoRandom`), so the tape is never read. -/
def zeroTape : Tape := fun _ => (0, 0)

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Theorems 7.1 and 7.3 (pp.27–28) and Lemma 6.3 (p.24), "classical post-processing takes … time
and … working memory": the run of a program of the published real RAM `MatMulTimeLP.RealRAM`
(exact `+ − × ÷ √`, index cells with `+ −`, indirect load/store, comparisons) from an initial state
`s₀`: the state after `t` steps.

**Formalization Note** The paper names no machine. Its proofs count arithmetic operations and use
`√` (normalizations, `2 × 2` eigenvectors, trace distances), so time is read on the unit-cost real
RAM with `√`. The published machine starts from an input of reals only and has no real-to-index
conversion, so the input is a **two-bank** initial state (`initState2`): integer data (the
register size, the circuit descriptions, the shot counts) in the index cells and the real data
(`ϵ`, `δ`, the histogram counts, complex vectors as real and imaginary parts) in the real cells.
**Time** is the number of executed instructions including the final `halt` (`HaltsWithin`).
**Working memory** is the number of distinct cells, of either bank, written before the program
halts (`cellsWritten`); overwritten input cells count. The output is read from the real cells at
the halting state (`outputVec`), the amplitude of `z` at offset `2·index(z)` (real part) and
`2·index(z) + 1` (imaginary part), with `index(z) = Σ_j z_j 2^{n−1−j}` (qubit `0` most
significant). Programs are restricted by `RationalLiterals` and `NoRandom`. -/
noncomputable def stateFrom (P : Program) (s₀ : State) : ℕ → State
  | 0 => s₀
  | t + 1 => step P zeroTape t (stateFrom P s₀ t)

/-- The two-bank initial state: program counter `0`, the real cells `R[0], R[1], …` holding
`reals`, the index cells `N[0], N[1], …` holding `nats`, every other cell `0`. -/
noncomputable def initState2 (reals : List ℝ) (nats : List ℕ) : State :=
  ⟨0, fun i => reals.getD i 0, fun i => nats.getD i 0⟩

/-- The run from `s₀` halts within time `T`: some `t` with `t + 1 ≤ T` (the `t` executed
instructions and the final `halt`) reaches a halted state. -/
def HaltsWithin (P : Program) (s₀ : State) (T : ℝ) : Prop :=
  ∃ t : ℕ, IsHalted P (stateFrom P s₀ t) ∧ ((t : ℝ) + 1) ≤ T

/-- The first step at which the run is halted (`0` if it never halts; every statement that reads
it also requires halting). -/
noncomputable def haltStep (P : Program) (s₀ : State) : ℕ :=
  sInf {t | IsHalted P (stateFrom P s₀ t)}

/-- The cell written by the instruction about to execute in state `s`: `(true, i)` for the real
cell `R[i]`, `(false, i)` for the index cell `N[i]`, `none` for jumps and `halt`. -/
def writtenAt (P : Program) (s : State) : Option (Bool × ℕ) :=
  match P[s.pc]? with
  | some (Instr.rconst i _) => some (true, i)
  | some (Instr.radd i _ _) => some (true, i)
  | some (Instr.rsub i _ _) => some (true, i)
  | some (Instr.rmul i _ _) => some (true, i)
  | some (Instr.rdiv i _ _) => some (true, i)
  | some (Instr.rsqrt i _) => some (true, i)
  | some (Instr.rload i _) => some (true, i)
  | some (Instr.rstore i _) => some (true, s.N i)
  | some (Instr.nconst i _) => some (false, i)
  | some (Instr.nadd i _ _) => some (false, i)
  | some (Instr.nsub i _ _) => some (false, i)
  | some (Instr.nload i _) => some (false, i)
  | some (Instr.nstore i _) => some (false, s.N i)
  | some (Instr.gauss i) => some (true, i)
  | some (Instr.unif i) => some (true, i)
  | _ => none

/-- Working memory: the number of distinct cells written at the steps before halting. -/
noncomputable def cellsWritten (P : Program) (s₀ : State) : ℕ :=
  ((Finset.range (haltStep P s₀)).biUnion fun t => (writtenAt P (stateFrom P s₀ t)).toFinset).card

/-- The halting state of the run. -/
noncomputable def finalState (P : Program) (s₀ : State) : State :=
  stateFrom P s₀ (haltStep P s₀)

/-- The position `index(z) = Σ_j z_j 2^{n−1−j}` of a bit string in the fixed order of `{0,1}ⁿ`
(qubit `0` most significant). -/
def bitsIndex {n : ℕ} (z : Bits n) : ℕ :=
  ∑ j : Fin n, (z j).val * 2 ^ (n - 1 - j.1)

/-- The bit string with index `k < 2ⁿ`. -/
def bitsOfIndex (n k : ℕ) : Bits n :=
  fun j => if k.testBit (n - 1 - j.1) then 1 else 0

/-- All bit strings of length `n` in index order. -/
def allBits (n : ℕ) : List (Bits n) :=
  (List.range (2 ^ n)).map (bitsOfIndex n)

/-- A complex vector as reals in index order, the real part of each amplitude followed by its
imaginary part. -/
noncomputable def complexList {n : ℕ} (v : Bits n → ℂ) : List ℝ :=
  (allBits n).flatMap fun z => [(v z).re, (v z).im]

/-- The output vector: at the halting state, the amplitude of `z` is
`R[off + 2·index(z)] + i·R[off + 2·index(z) + 1]`, where `off` is the length of the real input. -/
noncomputable def outputVec (P : Program) (s₀ : State) (off n : ℕ) : Bits n → ℂ :=
  fun z => ⟨(finalState P s₀).R (off + 2 * bitsIndex z), (finalState P s₀).R (off + 2 * bitsIndex z + 1)⟩

/-- Every real literal of the program is rational, so no real constant can encode a table. -/
def RationalLiterals (P : Program) : Prop :=
  ∀ (i : ℕ) (c : ℝ), Instr.rconst i c ∈ P → ∃ q : ℚ, c = q

/-- The program is deterministic: it draws no Gaussian and no uniform from the tape. -/
def NoRandom (P : Program) : Prop :=
  ∀ i : ℕ, Instr.gauss i ∉ P ∧ Instr.unif i ∉ P

end ShadowBootstrap


