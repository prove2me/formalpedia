-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_IsOccupancyZ
-- name    : MarkovEntanglementExact_Supplement_IsOccupancyZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:49:34.236912+00:00
-- url     : https://prove2.me/theorems/a9a4d1cd-4f60-4a5d-901c-755226a948ac
-- title:
--   Occupancy measure with exogenous information
-- statement:
--   A function $\mu$ on triples $(s,a,z)$ is an **occupancy measure with exogenous information** if $\mu\ge0$, $\sum\mu=1$ and every marginal $\mu_{iz}(s_i,a_i,z)$ is positive, so that the conditional $\mu(s_{-i},a_{-i}\mid s_i,a_i,z)$ in the local transition $P_{iz}$ is well defined.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Appendix J.1, p.45, with footnote 1, p.8

import Mathlib
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_MarkovEntanglementExact_Supplement_marginalDistZ

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- An occupancy measure of a system with exogenous information: a probability distribution `μ`
on `(s, a, z)` whose marginal `μ_{iz}(s_i, a_i, z)` is positive for every agent `i`, every pair
`(s_i, a_i)` and every `z`, so that the conditional `μ(s_{−i}, a_{−i} | s_i, a_i, z)` of the
local transition `P_{iz}` is well defined.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Appendix J.1, p.45,
with footnote 1, p.8.

**Formalization Note.** Positivity is on the `(s_i, a_i, z)` marginals, not on joint triples.
The paper's `μ^π_ABz` is the stationary distribution of a unichain system; neither stationarity
nor uniqueness is part of this definition, since Theorem 9's proof does not use them. -/
def IsOccupancyZ {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {Z : Type*} [Fintype Z] [DecidableEq Z] (μ : JointZ S Z → ℝ) : Prop :=
  (∀ p, 0 ≤ μ p) ∧ (∑ p, μ p = 1) ∧ ∀ (i : Fin N) (t : S i × Z), 0 < marginalDistZ i μ t

end MarkovEntanglementExact.Supplement


