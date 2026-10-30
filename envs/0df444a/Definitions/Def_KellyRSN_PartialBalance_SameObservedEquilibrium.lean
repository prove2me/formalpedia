-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_SameObservedEquilibrium
-- name    : KellyRSN_PartialBalance_SameObservedEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:41:19.572095+00:00
-- url     : https://prove2.me/theorems/83a3d745-7ae7-4f25-a3fa-7ef1359e519e
-- title:
--   Exit and entry chains of $\mathcal A$ have the same equilibrium distribution
-- statement:
--   For rates $q$ on $\mathcal S$ and $\mathcal A \subseteq \mathcal S$, the chain observed just before the process leaves $\mathcal A$ and the chain observed just after it enters $\mathcal A$ **have the same equilibrium distribution** if there is a distribution $\nu$ on $\mathcal A$ such that
--
--   1. $\nu$ is the unique equilibrium distribution of the exit chain $P^{\mathrm{exit}}$, and
--   2. $\nu$ is the unique equilibrium distribution of the entry chain $P^{\mathrm{entry}}$.
--
--   This is the property (vi) of Theorem 9.5.
--
--   **Formalization Note** "The equilibrium distribution" follows the book's convention that an equilibrium distribution is unique when it exists; each chain has exactly one and they coincide.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 33 (PDF p. 36), Exercise 1.7.8; p. 201 (PDF p. 204), Theorem 9.5 (vi)

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_exitKernel
import Definitions.Def_KellyRSN_PartialBalance_entryKernel
import Definitions.Def_KellyRSN_PartialBalance_IsStationaryProb

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **The exit chain and the entry chain of `𝒜` have the same equilibrium distribution.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.7.8, p. 33 (PDF p. 36) and
Theorem 9.5 (vi), p. 201 (PDF p. 204): "The Markov chain formed by observing the process at those
instants in time just before it leaves the set `𝒜` has the same equilibrium distribution as the
Markov chain formed by observing the process at those instants in time just after it enters the
set `𝒜`."

`SameObservedEquilibrium q A` says: there is a `ν` that is the **unique** equilibrium distribution
(`IsStationaryProb`) of the exit chain (`exitKernel q A`) and also the unique equilibrium
distribution of the entry chain (`entryKernel q A`).

**Formalization Note.** "The equilibrium distribution" follows the book's convention (§1.1, p. 2)
that an equilibrium distribution is unique when it exists: each chain has exactly one, and the two
are equal. Distributions are indexed by `↥A` and vanish on the states a chain never visits
(see `IsStationaryProb`). -/
def SameObservedEquilibrium {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (q : S → S → ℝ≥0∞) (A : Set S) : Prop :=
  ∃ ν : A → ℝ≥0∞, (∀ ν', IsStationaryProb (exitKernel q A) ν' ↔ ν' = ν) ∧
    (∀ ν', IsStationaryProb (entryKernel q A) ν' ↔ ν' = ν)

end KellyRSN.PartialBalance


