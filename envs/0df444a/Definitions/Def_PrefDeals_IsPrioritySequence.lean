-- Prove2me | Definitions.Def_PrefDeals_IsPrioritySequence
-- name    : PrefDeals_IsPrioritySequence
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:41.978714+00:00
-- url     : https://prove2.me/theorems/a5a8d431-436a-4b94-a2a6-06fdc5ef9b4b
-- title:
--   Admissible priority sequence of preferred deals
-- statement:
--   A list of (buyer, deal) pairs is an **admissible priority sequence** if
--
--   1. no buyer appears twice, and
--   2. every deal $(\rho,\mu,\mathcal I)$ has $0\le\mu\le1$ and a measurable set of impressions $\mathcal I$.
--
--   These are the sequences over which the seller optimizes.
--
--   **Formalization Note** A list may omit buyers: an omitted buyer earns what the empty deal at the end of the list earns, namely nothing, so the optimal revenue is the same as over full priority lists $(\pi_1,\dots,\pi_n)$.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, §3, p.8 ("The seller chooses a priority list $(\pi_1,\pi_2,\cdots,\pi_n)$")

import Mathlib
import Definitions.Def_PrefDeals_Deal

namespace PrefDeals

/-- **An admissible priority sequence of preferred deals.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, §3, p.8: "The seller chooses a
priority list `(π₁, π₂, …, πₙ)` where `n` denotes the number of buyers. The seller offers to each
buyer `i` a preferred deal `(ρᵢ, µᵢ, 𝓘ᵢ)`."

`IsPrioritySequence seq` says that the buyers listed in `seq` are distinct, and every deal has a
minimum purchase fraction `0 ≤ µ ≤ 1` and a measurable set of impressions.

**Formalization Note.** A list may omit buyers. A buyer not listed earns the same revenue as one
offered the empty deal `(0, 0, ∅)` at the end of the list, so the supremum of revenue over these
lists equals the supremum over full priority lists. -/
def IsPrioritySequence {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (seq : List (Fin n × Deal Ω)) : Prop :=
  (seq.map Prod.fst).Nodup ∧
    ∀ p ∈ seq, 0 ≤ p.2.minFrac ∧ p.2.minFrac ≤ 1 ∧ MeasurableSet p.2.impressions

end PrefDeals


