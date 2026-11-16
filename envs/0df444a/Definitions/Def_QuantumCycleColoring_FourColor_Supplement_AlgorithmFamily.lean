-- Prove2me | Definitions.Def_QuantumCycleColoring_FourColor_Supplement_AlgorithmFamily
-- name    : QuantumCycleColoring_FourColor_Supplement_AlgorithmFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:31:36.713339+00:00
-- url     : https://prove2.me/theorems/3416bb7d-d33a-4c3c-8a16-020414d7df62
-- title:
--   Cycle-length families of one-way one-round quantum algorithms and success with high probability
-- statement:
--   Fix a number of colours $q$. In a **one-way one-round anonymous quantum algorithm** on the directed $n$-cycle $v_\ell\to v_{\ell+1}$ ($\ell\in\mathbb Z_n$), every node prepares the same state on a kept register $A_\ell$ and a message register $B_\ell$, sends $B_\ell$ to its successor, and measures the same $q$-outcome POVM on the received register and its own, $B_{\ell-1}A_\ell$, outputting a colour $c_\ell\in[q]$. Since every node knows $n$, the algorithm may choose its data as a function of $n$.
--
--   1. An **algorithm family** assigns to every cycle length $n$ finite registers $A^{(n)}$, $B^{(n)}$, a density matrix $\rho_n$ (PSD, trace one) on $A^{(n)}\otimes B^{(n)}$, and a POVM $\{P^{(n)}_i\}_{i\in[q]}$ on $B^{(n)}\otimes A^{(n)}$. Private randomness, workspace and intermediate measurements are absorbed into the mixed state and the final POVM.
--   2. Its **success probability** on the $n$-cycle, $n\ge3$, is the Born-rule probability $\Pr[c_\ell\ne c_{\ell+1}\ \forall\ell]$ that the $n$ outputs form a proper $q$-colouring, computed from the published output law of the mission.
--   3. The family **succeeds with high probability** if there are constants $A>0$ and $k>0$ and a threshold $n_0\ge3$ such that
--   $$\Pr\big[\text{proper }q\text{-colouring of the }n\text{-cycle}\big]\ \ge\ 1-\frac{A}{n^{k}}\qquad\text{for every }n\ge n_0,$$
--   i.e. it fails with probability at most $1/\mathrm{poly}(n)$.
--
--   This is the solvability notion in statement (Q2) of Theorem 6.1: (Q2) says that no family succeeds with high probability.
--
--   **Formalization Note** Cycle lengths $n\ge3$ are written $n=m+3$, so the threshold is $n_0=m_0+3$. The data for $n<3$ are present in the structure but never used. The exponent $k$ is a positive real number, and $n^k$ is the real power.
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Definitions 3.8–3.10, pp.19–20 (high probability: Definition 3.8, p.19); Theorem 6.1 (Q2) and its proof, pp.40–42, footnote 10, p.42

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm

open scoped ComplexOrder

/-!
# Cycle-length families of one-way one-round algorithms and high-probability success

Tom Gur, Longcheng Li, *Impossibility of One-Way One-Round Quantum 4-Coloring via Matrix-Space
Stability*, STOC 2027 submission #515 (October 2026), Definitions 3.8–3.10 (pp.19–20) and
Theorem 6.1 (Q2), pp.40–42 with footnote 10.

Every node knows the cycle length `n` (Definition 3.8), so an algorithm may choose its finite
kept register `a n`, message register `b n`, prepared state `ρ n` and `q`-outcome POVM `P n` as a
function of `n`. Its output law on the directed `n`-cycle is the published Born-rule law
`properColoringProb`. Success with high probability (p.19) means success probability at least
`1 − 1/poly(n)`: here, at least `1 − A / n^k` for fixed `A > 0`, `k > 0` and all large `n`.
-/

namespace QuantumCycleColoring.FourColor.Supplement

open QuantumCycleColoring.FourColor Matrix

/-- Definitions 3.8–3.10, pp.19–20: a one-way one-round anonymous quantum algorithm for
`q`-colouring directed cycles, given for every cycle length `n` (the nodes know `n`): finite kept
and message registers `a n`, `b n`, a density matrix `ρ n` on `a n × b n` prepared by every node,
and a `q`-outcome POVM `P n` on `b n × a n` (received message register first) measured by every
node. The data for `n < 3` are present but never used. -/
structure AlgorithmFamily (q : ℕ) where
  /-- the kept register at cycle length `n` -/
  a : ℕ → Type
  /-- the message register at cycle length `n` -/
  b : ℕ → Type
  [fa : ∀ n, Fintype (a n)]
  [da : ∀ n, DecidableEq (a n)]
  [fb : ∀ n, Fintype (b n)]
  [db : ∀ n, DecidableEq (b n)]
  /-- the state every node prepares on `A_ℓ B_ℓ` -/
  ρ : ∀ n, Matrix (a n × b n) (a n × b n) ℂ
  /-- the POVM every node measures on `B_{ℓ-1} A_ℓ` -/
  P : ∀ n, Fin q → Matrix (b n × a n) (b n × a n) ℂ
  isDensity : ∀ n, IsDensityMatrix (ρ n)
  isPOVM : ∀ n, FuchsVdGraaf.IsPOVM (P n)

attribute [instance] AlgorithmFamily.fa AlgorithmFamily.da AlgorithmFamily.fb AlgorithmFamily.db

/-- The probability that the algorithm properly `q`-colours the directed cycle of length `m + 3`
(cycle lengths `n ≥ 3` are written `n = m + 3`). -/
noncomputable def AlgorithmFamily.successProb {q : ℕ} (F : AlgorithmFamily q) (m : ℕ) : ℝ :=
  properColoringProb (m + 3) (F.ρ (m + 3)) (F.P (m + 3))

/-- Definition 3.8, p.19: the algorithm succeeds with high probability, i.e. with probability
at least `1 − 1/poly(n)` on the directed `n`-cycle: there are constants `A > 0` and `k > 0`
(fixed before `n`) and a threshold such that for every cycle length `n = m + 3 ≥ m₀ + 3`,
`Pr[proper q-colouring] ≥ 1 − A / n^k`. -/
def AlgorithmFamily.SolvesWHP {q : ℕ} (F : AlgorithmFamily q) : Prop :=
  ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    1 - A / ((m + 3 : ℕ) : ℝ) ^ k ≤ F.successProb m

end QuantumCycleColoring.FourColor.Supplement


