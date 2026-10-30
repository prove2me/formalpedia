-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_piH
-- name    : MarketplaceLeakage_Communication_piH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:58:35.480379+00:00
-- url     : https://prove2.me/theorems/2587fdaa-3cde-4d1c-a153-5e8d53426959
-- title:
--   $\Pi_H(\eta)$: profit from the high-price option under a ban
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   The marketplace's profit from the **high-price option** under a ban is
--
--   $$
--   \Pi_H(\eta)=\eta q\,(v-c).
--   $$
--
--   It is obtained by setting the fee $f=v-c$: the seller then sets the price $p_m=v$ and sells only to the fraction $\eta q$ of buyers who learn that they value the product at $v$.
--
--   **Formalization Note** Defined for all real $q,v,c,\eta$; the statements that use it carry the model's ranges.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, unnumbered, p. 15 (option 1)

import Mathlib

namespace MarketplaceLeakage.Communication

/-- **`Π_H(η)`: the marketplace's profit from the high-price option under a ban.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, unnumbered, p. 15, option 1: "Set f = v − c, which induces S to choose the
high-price option, resulting in M making a profit of ΠH (η) = ηq (v − c)."

Here `q` is the buyers' prior probability of valuing the seller's product at `v`
("0 < q < 1", p. 14), `v` the value and `c` the marginal cost ("v > c", p. 5; "positive
marginal costs", p. 6), and `η` the probability that a buyer learns their valuation when
communication is banned ("from one to η ≤ 1", p. 14).

**Formalization Note.** Defined for all real arguments; statements carry the model's ranges. -/
noncomputable def piH (q v c η : ℝ) : ℝ := η * q * (v - c)

end MarketplaceLeakage.Communication


