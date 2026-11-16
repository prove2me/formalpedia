-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_singletonPay
-- name    : CompDesignBFM_Supplement_singletonPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:03:39.842609+00:00
-- url     : https://prove2.me/theorems/772ebe59-ff2f-4479-b005-b2476ae731f0
-- title:
--   The singleton compensation rule
-- statement:
--   Let $v$ be a value function, $B$ a budget and $\rho$ a fixed priority order on the agents. For a participating set $S\ne\emptyset$, the **singleton rule** pays the whole budget $B$ to the participant
--
--   $$i^*\in\arg\max_{i\in S}v(\{i\}),$$
--
--   ties broken in favour of the agent with smaller priority $\rho$, and pays zero to every other agent; on $S=\emptyset$ it pays nothing. It is the singleton branch of the randomized marginal-contribution rule (Algorithm 3.1).
--
--   **Formalization Note** The maximum is taken over the participants, never over costs, so the rule is cost oblivious. The priority $\rho:N\to\mathbb N$ is a parameter; for injective $\rho$ exactly one participant of a nonempty $S$ is paid.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Algorithm 3.1, lines 2–6, p.15 (PDF 17); Remark 2.1, p.12 (PDF 14)

import Mathlib

namespace CompDesignBFM

namespace Supplement

open Classical in
/-- The singleton compensation rule (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Algorithm 3.1, singleton branch, lines 2–6, p.15, PDF 17,
with the priority order of Remark 2.1, p.12, PDF 14): if `S ≠ ∅`, the agent `i* ∈ S` maximizing
`v({i})` over the participants is paid the whole budget `B`; every other agent is paid zero.
**Formalization Note.** Ties in `arg max_(i ∈ S) v({i})` are broken by the fixed agent priority `rho`
(smaller first), independent of costs; for injective `rho` exactly one agent of a nonempty `S` is paid.
The maximum is over the participating set `S`, not over affordable agents: the rule never sees costs.
`i ∈ S` already forces `S ≠ ∅`. -/
noncomputable def singletonPay {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (rho : Fin n → ℕ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S ∧ ∀ j ∈ S, v {j} < v {i} ∨ (v {j} = v {i} ∧ rho i ≤ rho j) then B else 0

end Supplement

end CompDesignBFM


