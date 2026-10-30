-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_entryKernel
-- name    : KellyRSN_PartialBalance_entryKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:58.996958+00:00
-- url     : https://prove2.me/theorems/d78abcd6-67f3-4682-9faf-309136c1bedc
-- title:
--   Chain observed just after the process enters $\mathcal A$
-- statement:
--   Let $q$ be rates on $\mathcal S$, $\mathcal A \subseteq \mathcal S$, and $\mathbb P_j$ the law of the jump chain started at $j$. The instants just after the process enters $\mathcal A$ are the **entry steps** of the jump chain, $\omega_m \notin \mathcal A$ and $\omega_{m+1} \in \mathcal A$; the observed state is $\omega_{m+1}$. The observed chain has transition probabilities
--   $$
--   P^{\mathrm{entry}}(j,j') = \mathbb P_j\bigl(\text{at the first entry step } m,\ \omega_{m+1} = j'\bigr), \qquad j, j' \in \mathcal A .
--   $$
--
--   **Formalization Note** Indexed by all of $\mathcal A$; states of $\mathcal A$ with no positive rate in from $\mathcal S - \mathcal A$ are never observed.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 33 (PDF p. 36), Exercise 1.7.8; p. 201 (PDF p. 204), Theorem 9.5 (vi)

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_jumpChainLaw

open MeasureTheory
open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Transition probabilities of the chain observed just after the process enters `𝒜`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.7.8, p. 33 (PDF p. 36) and
Theorem 9.5 (vi), p. 201 (PDF p. 204): "the Markov chain formed by observing the process at those
instants in time just after it enters the set `𝒜`".

The process enters `A` only at a jump, so these instants are the entry steps of the jump chain
`ω` (`ω m ∉ A`, `ω (m+1) ∈ A`), and the observed state is `ω (m+1) ∈ A`. From an entry at `j ∈ A`
the next observed state is the state just after the first entry step of the jump chain started at
`j`:

`entryKernel q A j j' = P_j(the first `m` with `ω m ∉ A, ω (m+1) ∈ A` has `ω (m+1) = j'`)`.

**Formalization Note.** The kernel is indexed by all of `↥A`; states of `A` with no positive rate
in from `𝒮 − 𝒜` are never observed, and the chain's equilibrium distribution vanishes there. The
entry step is written as `ω m ∉ A ∧ ω (m+1) ∈ A` to avoid natural-number subtraction. -/
noncomputable def entryKernel {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (q : S → S → ℝ≥0∞) (A : Set S) (j j' : A) : ℝ≥0∞ :=
  jumpChainLaw q j
    {ω | ∃ m, ω m ∉ A ∧ ω (m + 1) = (j' : S) ∧ ∀ i < m, ¬ (ω i ∉ A ∧ ω (i + 1) ∈ A)}

end KellyRSN.PartialBalance


