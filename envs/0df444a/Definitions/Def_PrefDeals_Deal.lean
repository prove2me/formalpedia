-- Prove2me | Definitions.Def_PrefDeals_Deal
-- name    : PrefDeals_Deal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:03.212433+00:00
-- url     : https://prove2.me/theorems/f5a70bab-293c-4015-b9a1-d3795426ba04
-- title:
--   Preferred deal $(\rho,\mu,\mathcal I)$
-- statement:
--   A **preferred deal** $(\rho,\mu,\mathcal I)$ consists of a price per impression $\rho\in\mathbb R$, a minimum purchase requirement $\mu$ (a fraction) and a set of impressions $\mathcal I\subseteq\Omega$. By accepting it, the buyer gains first-look access to the impressions in $\mathcal I$ and agrees to buy at least a fraction $\mu$ of them, each at price $\rho$.
--
--   The **empty deal** $(0,0,\emptyset)$ offers nothing; the Auction-Adjusted Greedy algorithm gives it to the buyers who never have the highest valuation.
--
--   **Formalization Note** The conditions $0\le\mu\le1$ and the measurability of $\mathcal I$ are imposed where deals are quantified over (admissible priority sequences), not in the structure.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, §2, p.5 (Preferred Deal), §3, p.8, and Figure 1, p.11 (empty deal)

import Mathlib

namespace PrefDeals

/-- **A preferred deal `(ρ, µ, 𝓘)`.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, §2, p.5: "A preferred deal for the
sequence of impressions `𝓘` is defined by two parameters, the price per impression `ρ` and the
minimum purchase requirement `µ`. By accepting the contract, the buyer gains first-look access to
the impressions in `𝓘` and agrees to buy at least a fraction `µ` of them, each at price `ρ`", and
§3, p.8: "The seller offers to each buyer `i` a preferred deal `(ρᵢ, µᵢ, 𝓘ᵢ)`."

A `Deal Ω` has a price per impression `price = ρ`, a minimum purchase fraction `minFrac = µ` and a
set of impressions `impressions = 𝓘 ⊆ Ω`. `Deal.empty` is the trivial deal `(0, 0, ∅)` of Figure 1,
p.11.

**Formalization Note.** The admissibility conditions `0 ≤ µ ≤ 1` and the measurability of `𝓘` are
not part of the structure; they are imposed where deals are quantified over
(`IsPrioritySequence`). -/
structure Deal (Ω : Type*) where
  /-- The price per impression `ρ`. -/
  price : ℝ
  /-- The minimum purchase requirement `µ`, a fraction of the impressions offered. -/
  minFrac : ℝ
  /-- The impressions `𝓘` the deal gives first-look access to. -/
  impressions : Set Ω

/-- The empty deal `(ρ = 0, µ = 0, 𝓘 = ∅)` of Figure 1, p.11. -/
def Deal.empty {Ω : Type*} : Deal Ω := ⟨0, 0, ∅⟩

end PrefDeals


