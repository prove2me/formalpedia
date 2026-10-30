-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_IsDecreasingOrder
-- name    : SeqPostedPricing_MatroidSPM_IsDecreasingOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:39:02.781038+00:00
-- url     : https://prove2.me/theorems/da1627bf-06d5-43f6-9ed5-9bb9f3e86af1
-- title:
--   Offers in decreasing order of price
-- statement:
--   An order $\sigma$ makes **offers in decreasing order of price** on a set of agents $\mathcal A$ if for all steps $t\le t'$ whose agents $\sigma(t),\sigma(t')$ lie in $\mathcal A$,
--
--   $$
--   p_{\sigma(t')}\le p_{\sigma(t)} .
--   $$
--
--   Ties between equal prices may be broken in any way.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6

import Mathlib

namespace SeqPostedPricing.MatroidSPM

/-- **Offers in decreasing order of price.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4, unnumbered, p. 6 (PDF p. 8): "The SPM sets a price of pi for agent i and offers to serve
the agents in decreasing order of their prices."

`IsDecreasingOrder p active σ`: along the steps, the prices of the active agents are
non-increasing: if step `t` comes no later than step `t'`, then `p (σ t') ≤ p (σ t)`.

**Formalization Note.** Ties are broken arbitrarily (the paper fixes no tie-break); inactive
agents are never offered and are not constrained. -/
def IsDecreasingOrder {n : ℕ} (p : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n) :
    Prop :=
  ∀ t t' : Fin n, t ≤ t' → σ t ∈ active → σ t' ∈ active → p (σ t') ≤ p (σ t)

end SeqPostedPricing.MatroidSPM


