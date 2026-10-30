-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_PrefersBan
-- name    : MarketplaceLeakage_Communication_PrefersBan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:01:24.930951+00:00
-- url     : https://prove2.me/theorems/f6136fde-bee1-4e4c-8ce4-5d0af10b7d97
-- title:
--   The marketplace prefers to ban communication
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Without a ban the marketplace's expected profit is $qP$, where $P=\Pi^*$ is its baseline equilibrium profit. With a ban it is $\max\{\Pi_H(\eta),\Pi_L(\eta)\}$. The marketplace **prefers to ban communication** when
--
--   $$
--   qP<\max\{\Pi_H(\eta),\Pi_L(\eta)\}.
--   $$
--
--   **Formalization Note** The preference is strict. The baseline profit is written $P$ in Lean.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, p. 15

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_banProfit

namespace MarketplaceLeakage.Communication

/-- **"The marketplace prefers to ban communication."**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, p. 15: "If M does not ban communication [...] M's expected profit is qΠ∗, where Π∗
is given by (3)." and "M's profit after banning communication is max {ΠH (η) , ΠL (η)}, which
needs to be compared to the profit qΠ∗ without any limits on communication."

`PrefersBan q v c η P` says the ban profit strictly exceeds the allow profit `q · P`, where
`P` stands for the baseline equilibrium profit `Π*`.

**Formalization Note.** The preference is strict (the paper does not discuss ties). The
baseline profit is named `P` because `Π` is reserved Lean syntax. -/
def PrefersBan (q v c η P : ℝ) : Prop := q * P < banProfit q v c η

end MarketplaceLeakage.Communication


