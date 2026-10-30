-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_IsStationaryProb
-- name    : KellyRSN_PartialBalance_IsStationaryProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:40:17.736288+00:00
-- url     : https://prove2.me/theorems/06b53328-aae1-47bf-87c9-af8d48568033
-- title:
--   Equilibrium distribution of a discrete-time chain (equations (1.1))
-- statement:
--   For transition probabilities $P(j,j')$ on a countable set $T$, a family $\nu(j)$, $j \in T$, is an **equilibrium (stationary) distribution** if
--   $$
--   \sum_{j \in T} \nu(j) = 1, \qquad \nu(j') = \sum_{j \in T} \nu(j)\, P(j,j'), \quad j' \in T. \tag{1.1}
--   $$
--
--   It is used for the chains observed at the exit and entry instants of a set $\mathcal A$.
--
--   **Formalization Note** Unlike the book's definition, positivity on all of $T$ is not required: the observed chains are indexed by $\mathcal A$ but visit only part of it, and their equilibrium distributions (positive on the states visited) are extended by $0$ to the rest of $\mathcal A$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 2 (PDF p. 5), §1.1, equations (1.1) and the definition of an equilibrium distribution

import Mathlib

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Equilibrium distribution of a discrete-time Markov chain (on the states it visits).**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, §1.1, p. 2 (PDF p. 5), equations (1.1):
"an equilibrium distribution, that is a collection of positive numbers `π(j)`, `j ∈ 𝒮`, summing to
unity that satisfy the equilibrium equations `π(j) = Σ_{k∈𝒮} π(k) p(k, j)`, `j ∈ 𝒮` (1.1)".

`IsStationaryProb P ν` says `Σ_j ν j = 1` and `ν j' = Σ_j ν j * P j j'` for every `j'`.

**Formalization Note.** Positivity is not required on the whole index type. The definition is used
for the chains observed at exit and entry instants of a set `𝒜`, indexed by `↥A`, which visit only
part of `A` (the states with a positive rate out of, respectively into, `A`); the book's
equilibrium distribution of such a chain is a positive distribution on the states it visits, and
here it is extended by `0` to the rest of `A`. -/
def IsStationaryProb {T : Type*} (P : T → T → ℝ≥0∞) (ν : T → ℝ≥0∞) : Prop :=
  ∑' j, ν j = 1 ∧ ∀ j', ∑' j, ν j * P j j' = ν j'

end KellyRSN.PartialBalance


