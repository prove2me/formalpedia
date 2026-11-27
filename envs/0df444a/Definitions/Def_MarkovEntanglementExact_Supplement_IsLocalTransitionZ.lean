-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_IsLocalTransitionZ
-- name    : MarkovEntanglementExact_Supplement_IsLocalTransitionZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:49:59.544848+00:00
-- url     : https://prove2.me/theorems/f3420ed5-371a-4417-ab01-cb7b368f0976
-- title:
--   Local transition $P_{iz}$ with exogenous information
-- statement:
--   $P_{iz}$ is agent $i$'s **local transition with exogenous information** for the joint transition $P$ and occupancy $\mu$ if
--   $$P_{iz}(s_i',a_i',z'\mid s_i,a_i,z)=\sum_{s_{-i},a_{-i}}\mu(s_{-i},a_{-i}\mid s_i,a_i,z)\sum_{s'_{-i},a'_{-i}}P(s',a',z'\mid s,a,z).$$
--   It is the transition each agent would fit from its own observations and the shared signal.
--
--   **Formalization Note** Both sides are multiplied by the marginal $\mu_{iz}(s_i,a_i,z)$; under positive marginals this is the same condition.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Appendix J.1, p.45

import Mathlib
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_MarkovEntanglementExact_Supplement_marginalDistZ

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- `Piz` is agent `i`'s local transition with exogenous information, obtained by marginalizing
the joint transition `P` over the other agents with the conditional occupancy:
`P_{iz}(s′_i, a′_i, z′ | s_i, a_i, z) = Σ_{s_{−i}, a_{−i}} μ(s_{−i}, a_{−i} | s_i, a_i, z)
 Σ_{s′_{−i}, a′_{−i}} P(s′, a′, z′ | s, a, z)`.
It is written multiplied by the marginal `μ_{iz}(s_i, a_i, z)`, so that no division appears.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Appendix J.1, p.45
(display defining `P_Az`, written for agent `A`).

**Formalization Note.** Under `IsOccupancyZ` (positive marginals) the multiplicative form is
equivalent to the paper's quotient form and determines `Piz` uniquely. `marginalZ i P p t` is the
published marginal of row `p` of `P` onto agent `i`'s next pair and the next exogenous state. -/
def IsLocalTransitionZ {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {Z : Type*} [Fintype Z] [DecidableEq Z] (i : Fin N)
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) (μ : JointZ S Z → ℝ)
    (Piz : Matrix (S i × Z) (S i × Z) ℝ) : Prop :=
  ∀ s t : S i × Z, marginalDistZ i μ s * Piz s t =
    ∑ p : JointZ S Z, (if p.1 i = s.1 ∧ p.2 = s.2 then μ p else 0) * marginalZ i P p t

end MarkovEntanglementExact.Supplement


