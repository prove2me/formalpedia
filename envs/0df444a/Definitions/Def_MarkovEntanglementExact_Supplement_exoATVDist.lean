-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_exoATVDist
-- name    : MarkovEntanglementExact_Supplement_exoATVDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:50:17.853797+00:00
-- url     : https://prove2.me/theorems/49620e5d-90d2-5409-b783-b46d4b57eeaf
-- title:
--   Agent-wise total variation distance with exogenous information
-- statement:
--   For agent $i$ and a candidate local transition $P_{iz}$ on agent $i$'s pairs and the exogenous states, the **agent-wise total variation distance** to the joint transition $P$ is
--   $$\max_{s,a,z}\tfrac12\sum_{s_i',a_i',z'}\big|P(s_i',a_i',z'\mid s,a,z)-P_{iz}(s_i',a_i',z'\mid s_i,a_i,z)\big|,$$
--   where $P(s_i',a_i',z'\mid s,a,z)$ is the marginal of row $(s,a,z)$ of $P$.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (13), p.46

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- The agent-wise total variation distance, for agent `i` of a system with exogenous
information, between the joint transition `P` and a candidate local transition `Piz` on agent
`i`'s pairs and the exogenous state:
`max_{s, a, z} ½ Σ_{s′_i, a′_i, z′} |P(s′_i, a′_i, z′ | s, a, z) − P_{iz}(s′_i, a′_i, z′ | s_i, a_i, z)|`,
where `P(s′_i, a′_i, z′ | s, a, z)` is the marginal of row `(s, a, z)` of `P` (published
`marginalZ`).

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (13), p.46 (the
expression under `min_{P_Az}`, written for agent `A`). -/
noncomputable def exoATVDist {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] {Z : Type*} [Fintype Z] [DecidableEq Z] (i : Fin N)
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) (Piz : Matrix (S i × Z) (S i × Z) ℝ) : ℝ :=
  ⨆ p : JointZ S Z, (1 / 2) * ∑ t : S i × Z, |marginalZ i P p t - Piz (p.1 i, p.2) t|

end MarkovEntanglementExact.Supplement


