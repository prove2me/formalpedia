-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_IsOccupancyN
-- name    : MarkovEntanglementExact_Supplement_IsOccupancyN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:47:50.687853+00:00
-- url     : https://prove2.me/theorems/9ecd465b-57f1-5190-b143-33d26570a62c
-- title:
--   Occupancy measure of an $N$-agent system with positive agent marginals
-- statement:
--   A function $\mu$ on the joint state-action pairs of $N$ agents is an **occupancy measure** if $\mu\ge0$, $\sum\mu=1$, and every agent marginal $\mu_i(s_i,a_i)=\sum_{(s,a):(s,a)_i=(s_i,a_i)}\mu(s,a)$ is positive. These are the conditions under which agent $i$'s local transition (Appendix H) is well defined.
--
--   **Formalization Note** Positivity is on agent marginals, not on joint pairs, as in footnote 1 and the published two-agent `IsOccupancy`.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Appendix H, p.40, with footnote 1, p.8

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- An occupancy measure of an `N`-agent system: a probability distribution `μ` on joint
state-action pairs whose marginal on every agent's state-action pairs is positive:
`μ ≥ 0`, `Σ μ = 1`, and `μ_i(s_i, a_i) > 0` for every agent `i` and every pair `(s_i, a_i)`.
These are the conditions under which the conditional `ρ^π_{1:N}(s_{−i}, a_{−i} | s_i, a_i)` of
Appendix H's local transition is well defined.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Appendix H, p.40
(local transition `P^π_i`), with footnote 1, p.8 (pairs of zero marginal are removed from the
feasible action set).

**Formalization Note.** Positivity is required of the agent marginals (`marginalDist`), not of
joint pairs: the paper's occupancy `μ(s)π(a | s)` vanishes on joint actions the policy never
plays. Stationarity is a separate hypothesis where a theorem uses it. This is the `N`-agent form
of the published two-agent `MarkovEntanglementExact.IsOccupancy`. -/
def IsOccupancyN {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : Joint S → ℝ) : Prop :=
  (∀ p, 0 ≤ μ p) ∧ (∑ p, μ p = 1) ∧ ∀ (i : Fin N) (s : S i), 0 < marginalDist i μ s

end MarkovEntanglementExact.Supplement


