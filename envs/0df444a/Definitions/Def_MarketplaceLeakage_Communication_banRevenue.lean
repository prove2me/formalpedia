-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_banRevenue
-- name    : MarketplaceLeakage_Communication_banRevenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:57.164991+00:00
-- url     : https://prove2.me/theorems/ebe20d98-b6bb-4a57-9f61-dfe427e43cd7
-- title:
--   The marketplace's revenue at fee $f$ under a ban, given the seller's best response
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Fix a fee $f$. Under a ban the seller compares the high-price profit $\eta q(v-c-f)$ with the low-price profit $(1-\eta+\eta q)(qv-c-f)$. It takes the high price if that profit is strictly larger, and the low price otherwise. It lists on the marketplace if the profit of its chosen option is nonnegative (its outside option is zero). The marketplace's revenue is
--
--   $$
--   R(f)=\begin{cases} f\,\eta q & \text{high price chosen and }\eta q(v-c-f)\ge 0,\\ f\,(1-\eta+\eta q) & \text{low price chosen and }(1-\eta+\eta q)(qv-c-f)\ge 0,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   This is the payoff whose maximum over $f$ the paper computes as $\max\{\Pi_H(\eta),\Pi_L(\eta)\}$.
--
--   **Formalization Note** The tie rule follows the page's "Otherwise, S chooses the second (low-price) option". The listing rule makes the seller list at zero profit, which is the case at the paper's option-1 fee $f=v-c$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, unnumbered, p. 15

import Mathlib

namespace MarketplaceLeakage.Communication

/-- **The marketplace's revenue at fee `f` under a ban, given the seller's best response.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, unnumbered, p. 15: "Suppose now M bans communication. Assuming S lists on M,
leakage is impossible so S's only relevant price is the on-platform price pm. It has two pricing
options. The first one is to set pm = v and only sell to the fraction ηq of buyers who learn that
their valuation of its product is v. Its resulting profit is ηq (v − c − f). The second option
for S is to set the lower price pm = qv, so that it also sells to the 1 − η buyers who never
learn their true valuation for its product. Its resulting profit in this case is
(1 − η + ηq) (qv − c − f). [...] Otherwise, S chooses the second (low-price) option."

The seller takes the high price when its profit there is strictly larger, and the low price
otherwise (the page's "Otherwise": ties go to the low price). The seller lists on the
marketplace when the profit of its chosen option is nonnegative (its outside option is zero;
at the paper's option-1 fee `f = v − c` the seller earns exactly zero and lists). The
marketplace then earns `f` per unit sold: `f · ηq` (high price) or `f · (1 − η + ηq)`
(low price), and `0` if the seller does not list.

**Formalization Note.** The tie rule and the listing rule are readings of the page, declared
in the items that use this definition. -/
noncomputable def banRevenue (q v c η f : ℝ) : ℝ :=
  if (1 - η + η * q) * (q * v - c - f) < η * q * (v - c - f) then
    (if 0 ≤ η * q * (v - c - f) then f * (η * q) else 0)
  else
    (if 0 ≤ (1 - η + η * q) * (q * v - c - f) then f * (1 - η + η * q) else 0)

end MarketplaceLeakage.Communication


