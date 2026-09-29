-- Prove2me | Definitions.Def_GittinsTerminalPotential
-- name    : GittinsTerminalPotential
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-08-01T15:51:40.82814+00:00
-- url     : https://prove2.me/theorems/e948fe19-9d97-4ffa-ab42-a91f3998606e
-- title:
--   Prevailing-charge terminal retirement potential
-- statement:
--   Consider a finite-armed rested Markov bandit.  After a finite history, the prevailing charge of arm $i$ is the least Gittins index exposed for that arm so far.  If $v(y,\gamma)$ is the single-arm retirement value at state $y$ and charge $\gamma$, define the terminal retirement potential by
--
--   $$
--   W_n=\sum_{i=1}^k v\!\left(S_i(n),\underline g_i(n)\right),
--   \qquad
--   U_n^\pi=\mathbb E_\pi[W_n].
--   $$
--
--   This module supplies the finite-history truncation, the prevailing charge, and the pathwise and expected terminal potentials used in the finite-horizon accounting step of the Gittins-index proof.
--
--   **Formalization Note** Histories are indexed from zero, and `markovBanditExpectedRetirementPotential` is the integral of the sum of armwise retirement values under the platform's finite-horizon bandit law.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, §35.4, proof of Theorem 35.9, Part 1 “Prevailing Charge”, printed pp. 451–452 / PDF pp. 459–460, especially the definition of the prevailing charge and the retirement-value accounting identity.

import Definitions.Def_GittinsFiniteRetirementValue
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

/-- Forget the most recently completed bandit round while retaining the state
vector observed at the start of that round. -/
def truncateMarkovBanditHistory
    {k n : ℕ} {S : Type*} :
    MarkovBanditHistory k S (n + 1) → MarkovBanditHistory k S n :=
  fun h ↦ (Fin.init h.1, (h.1 (Fin.last n)).1)

/-- The least Gittins charge exposed for an arm by the end of a finite
history.  This is the prevailing charge in the proof of the index theorem. -/
noncomputable def currentHistoryPrevailingCharge
    {k : ℕ} {S : Type*} (g : S → ℝ) :
    (n : ℕ) → MarkovBanditHistory k S n → Fin k → ℝ
  | 0, h, i => g (h.2 i)
  | n + 1, h, i =>
      min
        (currentHistoryPrevailingCharge g n
          (truncateMarkovBanditHistory h) i)
        (g (h.2 i))

/-- Sum of the single-arm retirement values at the prevailing charges visible
after a finite bandit history. -/
noncomputable def currentGittinsRetirementPotential
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (h : MarkovBanditHistory k S n) : ℝ :=
  ∑ i : Fin k,
    gittinsRetirementValue P r α
      (currentHistoryPrevailingCharge
        (gittinsIndex P r α) n h i)
      (h.2 i)

/-- Expected terminal retirement potential after `n` rounds under a bandit
policy. -/
noncomputable def markovBanditExpectedRetirementPotential
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (n : ℕ) : ℝ :=
  ∫ h, currentGittinsRetirementPotential P r α h
    ∂markovBanditMeasure P π x n

end BanditAlgorithm


