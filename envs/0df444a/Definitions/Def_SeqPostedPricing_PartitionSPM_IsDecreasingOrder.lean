-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_IsDecreasingOrder
-- name    : SeqPostedPricing_PartitionSPM_IsDecreasingOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:11:37.316576+00:00
-- url     : https://prove2.me/theorems/d33abd22-d14f-43ff-8581-0123681e2cc4
-- title:
--   Offering in decreasing order of price
-- statement:
--   An order $\sigma$ offers the active agents **in decreasing order of their prices** if, whenever step $t$ comes no later than step $t'$ and both agents are active, $p_{\sigma(t')} \le p_{\sigma(t)}$. Ties may be broken in any way.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, p. 6 (PDF p. 8)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

/-- **Offers in decreasing order of price** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, p. 6 = PDF p. 8: "offers to serve the agents in
decreasing order of their prices"). Along the steps, the prices of the active agents are
non-increasing: if step `t` comes no later than step `t'`, then `p (σ t') ≤ p (σ t)`.

**Formalization Note** Reading 6 of the mission: ties are broken arbitrarily, since the paper fixes no
tie-break. Only active agents are compared. -/
def IsDecreasingOrder {n : ℕ} (p : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n) : Prop :=
  ∀ t t' : Fin n, t ≤ t' → σ t ∈ active → σ t' ∈ active → p (σ t') ≤ p (σ t)

end SeqPostedPricing.PartitionSPM


