-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_PrefersAllow
-- name    : MarketplaceLeakage_Communication_PrefersAllow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:02:12.404383+00:00
-- url     : https://prove2.me/theorems/2a478b36-8222-4916-a6f6-16621c9ab1e1
-- title:
--   The marketplace prefers to allow communication
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   The marketplace **prefers to allow communication** when its profit without a ban, $qP$ with $P=\Pi^*$, strictly exceeds its profit with a ban:
--
--   $$
--   \max\{\Pi_H(\eta),\Pi_L(\eta)\}<qP.
--   $$
--
--   **Formalization Note** The preference is strict. The baseline profit is written $P$ in Lean.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, p. 15; Proposition 3, p. 16

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_banProfit

namespace MarketplaceLeakage.Communication

/-- **"The marketplace prefers to allow communication."**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, p. 15–16: the ban profit `max {ΠH (η) , ΠL (η)}` is compared with the profit
`qΠ∗` without any limits on communication; Proposition 3 (p. 16) speaks of the marketplace
preferring to "ban (allow) communication".

`PrefersAllow q v c η P` says the allow profit `q · P` strictly exceeds the ban profit.

**Formalization Note.** The preference is strict (the paper does not discuss ties). The
baseline profit is named `P` because `Π` is reserved Lean syntax. -/
def PrefersAllow (q v c η P : ℝ) : Prop := banProfit q v c η < q * P

end MarketplaceLeakage.Communication


