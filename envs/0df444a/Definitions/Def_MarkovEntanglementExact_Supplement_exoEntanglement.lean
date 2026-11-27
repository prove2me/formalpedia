-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_exoEntanglement
-- name    : MarkovEntanglementExact_Supplement_exoEntanglement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:50:43.260933+00:00
-- url     : https://prove2.me/theorems/afa7c520-bd15-4f1e-84d5-c4c2a59f99e0
-- title:
--   Measure of Markov entanglement with exogenous information $E_i(P,\mathcal Z)$
-- statement:
--   The **measure of Markov entanglement of agent $i$ with exogenous information** is (Eq. (13))
--   $$E_i(P,\mathcal Z)=\min_{P_{iz}}\max_{s,a,z}\tfrac12\sum_{s_i',a_i',z'}\big|P(s_i',a_i',z'\mid s,a,z)-P_{iz}(s_i',a_i',z'\mid s_i,a_i,z)\big|,$$
--   the minimum over transition matrices $P_{iz}$. It is the measure of Theorem 9.
--
--   **Formalization Note** The reduced (second) form of Eq. (13), written as `sInf`; the minimum is attained.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (13), p.46

import Mathlib
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_MarkovEntanglementExact_Supplement_exoATVDist

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- The measure of Markov entanglement `E_i(P, 𝒵)` of agent `i` with exogenous information,
with respect to the agent-wise total variation distance (Eq. (13), written for agent `A`):
`E_i(P, 𝒵) = min_{P_{iz}} max_{s, a, z} ½ Σ_{s′_i, a′_i, z′} |P(s′_i, a′_i, z′ | s, a, z) −
P_{iz}(s′_i, a′_i, z′ | s_i, a_i, z)|`, the minimum over transition matrices `P_{iz}` on agent
`i`'s pairs and the exogenous state.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (13), p.46.

**Formalization Note.** This is the second, explicit form of Eq. (13). The printed first form,
`min ½ ‖P − Σ_j x_j P^(j)_{Az} ⊗ P^(j)_B‖_{ATV_1}`, carries an extra `½` in front of an agent-wise
distance that already contains it; the second form is the analogue of Eq. (5) and is the one under
which Theorem 9 holds. The minimum is over transition matrices and is written `sInf` of a nonempty
set bounded below by `0`; it is attained by compactness. -/
noncomputable def exoEntanglement {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] {Z : Type*} [Fintype Z] [DecidableEq Z] (i : Fin N)
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) : ℝ :=
  sInf {d : ℝ | ∃ Piz : Matrix (S i × Z) (S i × Z) ℝ,
    IsTransitionMatrix Piz ∧ d = exoATVDist i P Piz}

end MarkovEntanglementExact.Supplement


