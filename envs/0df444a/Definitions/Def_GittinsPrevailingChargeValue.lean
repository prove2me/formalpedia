-- Prove2me | Definitions.Def_GittinsPrevailingChargeValue
-- name    : GittinsPrevailingChargeValue
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-08-01T16:17:32.029787+00:00
-- url     : https://prove2.me/theorems/96e4d004-e134-45d7-910c-8ca6e31a80e3
-- title:
--   Finite discounted prevailing-charge value
-- statement:
--   For a finite-armed rested Markov bandit, the prevailing charge of an arm after a history is the least Gittins index exposed for that arm so far.  This module defines the expected prevailing charge selected in round $n$ and its finite discounted total
--
--   $$
--   C_N^\pi=\sum_{n<N}\alpha^n\,\mathbb E_\pi[\underline g_{A_n}(n)].
--   $$
--
--   The quantity $C_N^\pi$ is the common interface between the retirement-value accounting argument and the deterministic greedy-interleaving comparison.
--
--   **Formalization Note** The expectation is taken over the platform's one-step product of the finite-history law and the policy/transition kernel.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, §35.4, proof of Theorem 35.9, Part 1 “Prevailing Charge”, printed pp. 451–452 / PDF pp. 459–460.

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

/-- Expected prevailing charge selected in round `n`. -/
noncomputable def markovBanditRoundPrevailingCharge
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (n : ℕ) : ℝ :=
  ∫ p, currentHistoryPrevailingCharge
      (gittinsIndex P r α) n p.1 p.2.1
    ∂(markovBanditMeasure P π x n).compProd
      (markovBanditStepKernel P π n)

/-- Finite discounted sum of expected prevailing charges. -/
noncomputable def markovBanditFinitePrevailingChargeValue
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    α ^ n * markovBanditRoundPrevailingCharge P r α π x n

end BanditAlgorithm


