-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_IsCoverWitness
-- name    : FoundationsRL_DECExamples_IsCoverWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:48.112756+00:00
-- url     : https://prove2.me/theorems/c3a09fed-a2a9-4a27-85bd-2d36333b8109
-- title:
--   $\Pi'$ witnesses the covering number $\mathcal N_\rho(\Pi,\varepsilon)$
-- statement:
--   A finite set $\Pi'\subseteq\Pi$ **witnesses the covering number** $\mathcal N_\rho(\Pi,\varepsilon)$ if it is an $\varepsilon$-cover,
--
--   $$
--   \forall\pi\in\Pi\;\exists\pi'\in\Pi'\;\;\rho(\pi,\pi')\le\varepsilon,
--   $$
--
--   and $|\Pi'|=\mathcal N_\rho(\Pi,\varepsilon)$, that is, no smaller $\varepsilon$-cover exists. Step 1 of the strategy of Proposition 18 picks such a set.
--
--   **Formalization Note** `Metric.IsCover` uses the non-strict inequality $\rho\le\varepsilon$, as the notes do.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.3.3, p. 73, and Proposition 18, step 1, p. 73

import Mathlib
open scoped NNReal

namespace FoundationsRL.DECExamples

/-- `D' ⊆ D` witnesses the covering number `N_ρ(D, ε)`: it is an `ε`-cover, meaning
`∀ π ∈ D, ∃ π' ∈ D', ρ(π, π') ≤ ε`, of the smallest size.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §4.3.3, pp. 73–74.

**Formalization Note.** `Metric.IsCover` uses the non-strict `edist x y ≤ ε`, as the notes do. -/
def IsCoverWitness {D : Type*} [MetricSpace D] (ε : ℝ≥0) (D' : Finset D) : Prop :=
  Metric.IsCover ε Set.univ (D' : Set D) ∧
    (D'.card : ℕ∞) = Metric.coveringNumber ε (Set.univ : Set D)

end FoundationsRL.DECExamples


