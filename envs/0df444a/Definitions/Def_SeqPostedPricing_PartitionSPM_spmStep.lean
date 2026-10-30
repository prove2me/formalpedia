-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_spmStep
-- name    : SeqPostedPricing_PartitionSPM_spmStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:46.035178+00:00
-- url     : https://prove2.me/theorems/d1a10d2d-526d-4712-9a69-e0f1240190ec
-- title:
--   One step of a sequential posted-price mechanism
-- statement:
--   Let $A$ be the set of agents served so far, $p_i$ the posted prices, and let some agents be marked active. In one step of a **sequential posted-price mechanism**, agent $i$ is offered service at price $p_i$ if it is active and $A \cup \{i\}$ is feasible; it accepts if and only if the price is no more than its value, $p_i \le v_i$, and then $A$ becomes $A \cup \{i\}$. Otherwise $A$ is unchanged.
--
--   **Formalization Note** Only active agents are offered; the mechanism $S$ of §4 marks active exactly the agents served with positive probability by the optimal mechanism.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, step 2, p. 4 (PDF p. 6); §1, p. 1 (PDF p. 3)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

open Classical in
/-- **One step of a sequential posted-price mechanism** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, p. 4 = PDF p. 6, step 2:
"(a) If A ∪ {σ(i)} ∈ J, offer to serve agent σ(i) at price pi. (b) If the agent accepts,
A ← A ∪ {σ(i)}"; §1, p. 1 = PDF p. 3: "A rational agent will accept if and only if the price is no
more than their private value for service"). With served set `A`, agent `i` is offered service when
it is active and `A ∪ {i}` is feasible, and it accepts when `p i ≤ v i`.

**Formalization Note** Only agents in `active` are offered (Reading 4: the mechanism S offers no
agent whose service probability is `0`). Acceptance is `p_i ≤ v_i` (Reading 5). -/
noncomputable def spmStep {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (v : Fin n → ℝ) (A : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  if i ∈ active ∧ Feas (insert i A) ∧ p i ≤ v i then insert i A else A

end SeqPostedPricing.PartitionSPM


