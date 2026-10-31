-- Prove2me | Definitions.Def_ImbalPricing_IsPureNash
-- name    : ImbalPricing_IsPureNash
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:46.291311+00:00
-- url     : https://prove2.me/theorems/95719e68-becd-4bc2-930d-6230124c1a18
-- title:
--   Pure-strategy Nash equilibrium with constrained strategy sets
-- statement:
--   Consider a game in normal form with players $i\in I$. Player $i$ chooses a strategy $x_i$ from a set $S_i$, and $u_i(x)$ is the payoff of player $i$ at the strategy profile $x=(x_j)_{j\in I}$; every player wants a high payoff. For a profile $x$ and a strategy $a$ write $(a,x_{-i})$ for the profile in which player $i$ plays $a$ and every other player keeps $x_j$.
--
--   A profile $x$ is a **pure Nash equilibrium** if $x_i\in S_i$ for every $i$ and no player gains from a unilateral deviation:
--
--   $$u_i(a,x_{-i})\le u_i(x)\qquad\text{for every player } i \text{ and every } a\in S_i.$$
--
--   In this mission the players are the low-cost generators of an electricity market, the strategies are their Stage-1 offer adjustments and the payoffs their expected profits (see the market and optimal-pricing definitions). The paper uses this notion without defining it formally.
--
--   **Formalization Note** The deviated profile $(a,x_{-i})$ is `Function.update x i a`.
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §3.1.4, p.7 and Theorem 5, p.13 (PDF pp.9, 15): the equilibrium notion of the offer game (not defined formally in the paper)

import Mathlib

namespace ImbalPricing

/-- **Pure-strategy Nash equilibrium** of a game in normal form with constrained strategy sets.
Players are indexed by `ι`; player `i` chooses a strategy in the set `S i ⊆ A`, and `u i x` is
the payoff of player `i` (to be maximized) at the strategy profile `x : ι → A`.

A profile `x` is a pure Nash equilibrium if every coordinate is feasible, `x i ∈ S i`, and no
player gains from a unilateral deviation to another feasible strategy: for every `i` and every
`a ∈ S i`, `u i (x[i ↦ a]) ≤ u i x`.

This general object is used in Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, *Optimal Electricity
Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators*, MSOM
Articles in Advance (2023), §3.1.4 and Theorem 5, pp.7 and 13 (PDF pp.9 and 15), for the offer
game of the low-cost generators; the paper uses the notion without a formal definition.

**Formalization Note.** The profile with player `i`'s strategy replaced by `a` is
`Function.update x i a`. -/
def IsPureNash {ι A : Type*} [DecidableEq ι] (S : ι → Set A) (u : ι → (ι → A) → ℝ)
    (x : ι → A) : Prop :=
  (∀ i, x i ∈ S i) ∧ ∀ i, ∀ a ∈ S i, u i (Function.update x i a) ≤ u i x

end ImbalPricing


