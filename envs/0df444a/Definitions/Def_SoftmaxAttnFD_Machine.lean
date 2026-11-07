-- Prove2me | Definitions.Def_SoftmaxAttnFD_Machine
-- name    : SoftmaxAttnFD_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:47.11294+00:00
-- url     : https://prove2.me/theorems/88a28b37-7687-42b5-8450-8836afcda57e
-- title:
--   Runs, fair-coin tape, bit cost; Las Vegas and deterministic bit-cost bounds on the log-cost RAM
-- statement:
--   The machine is the published logarithmic-cost RAM `TimeSpaceMA_RAM`, reused as is. A **program** is a finite list of instructions over memory cells that hold natural numbers: load a constant, add, truncated subtraction, indirect load, indirect store, conditional jump, read the next fair coin into a cell, and halt. No instruction carries a function, so a program is a finite syntactic object.
--
--   Each executed instruction costs $1$ plus the bit lengths of every address it uses and every value it reads or writes. A program counter outside the program is stuck, and the run never halts. There is no multiplication, division or real-valued cell. This item defines, on that machine, the state after $T$ steps.
--
--   The coins form an infinite sequence $\tau$ of independent fair bits. The **cost** of a run on tape $\tau$ is the accumulated work at the first halted state, and $+\infty$ if the run never halts.
--
--   A program is **Las Vegas within expected cost** $\mathrm{bd}$ for a correctness predicate if on every tape on which the run halts the final memory is correct, and $\mathbb E_\tau[\mathrm{cost}]\le \mathrm{bd}$. It is **deterministic within cost** $\mathrm{bd}$ if it has no coin instruction and on every tape the cost is at most $\mathrm{bd}$ and the final memory is correct.
--
--   This is the reading of the paper's "We measure complexity in bit operations" and "Our randomized algorithms are Las Vegas, and their running times are measured in expectation". The paper names no machine.
--
--   **Formalization Note** A logarithmic-cost RAM keeps both constraints of the page: the running time counts bits, and random access does not cost polynomial factors in $m+n$, which the algorithm's data structures need. Arithmetic is programmable at polynomial overhead in the bit lengths. `Measurable` is part of the Las Vegas predicate because the Lean integral is a lower integral; it holds for every program.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), §2.1, p.11

import Definitions.Def_TimeSpaceMA_RAM

open MeasureTheory
open scoped ENNReal

namespace SoftmaxAttnFD

/-- The state after `T` steps from memory `mem` on tape `τ`, for a program of the logarithmic-cost
RAM with fair coins `TimeSpaceMA.Program` (published definition `TimeSpaceMA_RAM`, reused here:
each executed instruction costs 1 plus the bit lengths of every address used and every value read
or written; a halted state stays; an invalid program counter is stuck and never halts).

Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055, sha256
a60f7609…, §2.1, p.11: "We measure complexity in bit operations".

**Formalization Note** The page names no machine. The reused machine has no multiplication,
division, shift or real cell: all arithmetic is programmable at polylogarithmic overhead in the bit
lengths, which the soft-O absorbs, so leaving them out only makes an upper bound harder. Random
access is needed because the algorithm uses Fenwick trees and persistent dictionaries; a multitape
machine could change the exponent. -/
def run (P : TimeSpaceMA.Program) (mem : ℕ → ℕ) (τ : ℕ → Bool) (T : ℕ) : TimeSpaceMA.State :=
  (P.step τ)^[T] (TimeSpaceMA.State.init mem)

/-- The fair-coin tape: independent uniform bits, indexed by `ℕ`. -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

open Classical in
/-- Bit cost of the run on tape `τ`: the `work` at the first halted state, and `⊤` on a tape on which
the run never halts. -/
noncomputable def cost (P : TimeSpaceMA.Program) (mem : ℕ → ℕ) (τ : ℕ → Bool) : ℝ≥0∞ :=
  if h : ∃ T, (run P mem τ T).halted = true then
    ((run P mem τ (Nat.find h)).work : ℝ≥0∞)
  else ⊤

open Classical in
/-- The memory at the first halted state. On a non-halting tape it is the input memory, a value that
is never read: `LasVegasWithin` and `DeterministicWithin` constrain it only where `cost` is finite. -/
noncomputable def final (P : TimeSpaceMA.Program) (mem : ℕ → ℕ) (τ : ℕ → Bool) : ℕ → ℕ :=
  if h : ∃ T, (run P mem τ T).halted = true then
    (run P mem τ (Nat.find h)).mem
  else mem

/-- Las Vegas within expected bit cost `bd` (arXiv:2611.06055, §2.1, p.11: "Our randomized
algorithms are Las Vegas, and their running times are measured in expectation"): on every tape on
which the run halts the output is correct, and the expected cost is at most `bd`.

**Formalization Note** `cost` is `⊤` on a non-halting tape, so the bound forces halting with
probability one. `Measurable` is a conjunct because `∫⁻` is a lower integral; it holds for every
program. -/
def LasVegasWithin (P : TimeSpaceMA.Program) (mem : ℕ → ℕ) (good : (ℕ → ℕ) → Prop) (bd : ℝ) :
    Prop :=
  (∀ τ, cost P mem τ < ⊤ → good (final P mem τ)) ∧
    Measurable (cost P mem) ∧
    ∫⁻ τ, cost P mem τ ∂coinTape ≤ ENNReal.ofReal bd

/-- Deterministic within bit cost `bd`: the program has no `coin`, and on every tape the run halts
within cost `bd` with a correct output. -/
def DeterministicWithin (P : TimeSpaceMA.Program) (mem : ℕ → ℕ) (good : (ℕ → ℕ) → Prop)
    (bd : ℝ) : Prop :=
  P.CoinFree ∧ ∀ τ, cost P mem τ ≤ ENNReal.ofReal bd ∧ good (final P mem τ)

end SoftmaxAttnFD


