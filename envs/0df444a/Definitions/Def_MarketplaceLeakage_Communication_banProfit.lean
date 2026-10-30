-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_banProfit
-- name    : MarketplaceLeakage_Communication_banProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:40.791274+00:00
-- url     : https://prove2.me/theorems/dad95472-e0c7-4566-a0d2-d6bc3fe2716d
-- title:
--   The marketplace's profit after banning communication, $\max\{\Pi_H(\eta),\Pi_L(\eta)\}$
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   The marketplace's profit after banning communication is
--
--   $$
--   \max\{\Pi_H(\eta),\Pi_L(\eta)\}.
--   $$
--
--   It is compared with the profit $q\Pi^*$ the marketplace earns without any limits on communication.
--
--   **Formalization Note** At $\eta=1$, where the paper's $\Pi_L$ is undefined, Lean's $\Pi_L(1)=-qc<0\le\Pi_H(1)$, so the value is $\Pi_H(1)=q(v-c)$, which is the paper's ban profit at $\eta=1$ (proof of Proposition 3, p. 38).
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, unnumbered, p. 15

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_piH
import Definitions.Def_MarketplaceLeakage_Communication_piL

namespace MarketplaceLeakage.Communication

/-- **The marketplace's profit after banning communication, `max{Π_H(η), Π_L(η)}`.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, unnumbered, p. 15: "Thus, M's profit after banning communication is
max {ΠH (η) , ΠL (η)}, which needs to be compared to the profit qΠ∗ without any limits on
communication."

**Formalization Note.** At `η = 1` the paper's `Π_L` is undefined and Lean's `piL` equals
`−qc < 0 ≤ Π_H(1)` (for `q > 0`, `c > 0`, `v > c`), so `banProfit` at `η = 1` is
`Π_H(1) = q(v − c)`. This is the paper's ban profit at `η = 1` ("when η = 1, profits are
q (v − c)", §8.4, p. 38). That M's optimal fee earns this value is the milestone
`ban_profit_is_max`. -/
noncomputable def banProfit (q v c η : ℝ) : ℝ := max (piH q v c η) (piL q v c η)

end MarketplaceLeakage.Communication


