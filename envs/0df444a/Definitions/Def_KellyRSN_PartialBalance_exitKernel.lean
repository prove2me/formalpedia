-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_exitKernel
-- name    : KellyRSN_PartialBalance_exitKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:35.225793+00:00
-- url     : https://prove2.me/theorems/c6602077-a417-4dfc-9816-2bf3ce05db7a
-- title:
--   Chain observed just before the process leaves $\mathcal A$
-- statement:
--   Let $q$ be rates on $\mathcal S$, $\mathcal A \subseteq \mathcal S$, and $\mathbb P_k$ the law of the jump chain started at $k$. The process leaves $\mathcal A$ only at a jump, so the instants just before it leaves $\mathcal A$ are the **exit steps** $m$ of the jump chain, with $\omega_m \in \mathcal A$ and $\omega_{m+1} \notin \mathcal A$; the observed state is $\omega_m$. The observed chain has transition probabilities
--   $$
--   P^{\mathrm{exit}}(j,j') = \sum_{k \notin \mathcal A} \frac{q(j,k)}{\sum_{k' \notin \mathcal A} q(j,k')}\; \mathbb P_k\bigl(\text{the first exit step } m \text{ has } \omega_m = j'\bigr), \qquad j, j' \in \mathcal A:
--   $$
--   from an exit at $j$ the process jumps to $k \notin \mathcal A$, and the next observation is the state at the next exit.
--
--   **Formalization Note** Indexed by all of $\mathcal A$. A state of $\mathcal A$ with no positive rate out of $\mathcal A$ is never observed and gets the zero row ($0/0 = 0$ in $[0,\infty]$).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 33 (PDF p. 36), Exercise 1.7.8; p. 201 (PDF p. 204), Theorem 9.5 (vi)

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_jumpChainLaw

open MeasureTheory
open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Transition probabilities of the chain observed just before the process leaves `𝒜`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.7.8, p. 33 (PDF p. 36) and
Theorem 9.5 (vi), p. 201 (PDF p. 204): "the Markov chain formed by observing the process at those
instants in time just before it leaves the set `𝒜`".

The process leaves `A` only at a jump, so these instants are the exit steps `m` of the jump chain
`ω` (`ω m ∈ A`, `ω (m+1) ∉ A`), and the observed state is `ω m ∈ A`. From an exit at `j ∈ A` the
process moves to `k ∉ A` with probability `q(j, k) / Σ_{k' ∉ A} q(j, k')`, and the next observed
state is the state at the first exit step of the jump chain started at `k`:

`exitKernel q A j j' = Σ_{k ∉ A} (q(j, k) / Σ_{k' ∉ A} q(j, k')) ·
  P_k(the first `m` with `ω m ∈ A, ω (m+1) ∉ A` has `ω m = j'`)`.

**Formalization Note.** The kernel is indexed by all of `↥A`. A state `j ∈ A` with no positive rate
out of `A` is never observed; its row is `0` (`0/0 = 0` in `ℝ≥0∞`). If the jump chain from `k` never
exits again the row loses that mass; under the hypotheses of Theorem 9.5 (recurrence) this does not
happen. -/
noncomputable def exitKernel {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (q : S → S → ℝ≥0∞) (A : Set S) (j j' : A) : ℝ≥0∞ :=
  ∑' k : ↥Aᶜ, (q j k / ∑' k' : ↥Aᶜ, q j k') *
    jumpChainLaw q k
      {ω | ∃ m, ω m = (j' : S) ∧ ω (m + 1) ∉ A ∧ ∀ i < m, ¬ (ω i ∈ A ∧ ω (i + 1) ∉ A)}

end KellyRSN.PartialBalance


