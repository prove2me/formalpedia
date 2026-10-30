-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_highPriceThreshold
-- name    : MarketplaceLeakage_Communication_highPriceThreshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:58:54.194927+00:00
-- url     : https://prove2.me/theorems/e29e3bea-463e-4419-beb6-6b7f40853057
-- title:
--   The seller's indifference fee $\frac{(1-(2-q)\eta)qv}{1-\eta}-c$ under a ban
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Under a ban the seller either sets $p_m=v$ (profit $\eta q(v-c-f)$) or $p_m=qv$ (profit $(1-\eta+\eta q)(qv-c-f)$). The fee at which it is indifferent is
--
--   $$
--   \bar f(\eta)=\frac{(1-(2-q)\eta)\,qv}{1-\eta}-c .
--   $$
--
--   The seller prefers the high price exactly when $f>\bar f(\eta)$; $\bar f(\eta)$ is also the fee of the marketplace's option 2.
--
--   **Formalization Note** The formula divides by $1-\eta$ and is undefined at $\eta=1$; Lean's convention $x/0=0$ gives the value $-c$ there, and every statement that uses the threshold assumes $\eta<1$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, unnumbered, p. 15

import Mathlib

namespace MarketplaceLeakage.Communication

/-- **The seller's indifference fee under a ban.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, unnumbered, p. 15: "S prefers the first (high-price) option if and only if
f > (1 − (2 − q) η) qv/(1 − η) − c. Otherwise, S chooses the second (low-price) option."
It is also the fee of the marketplace's option 2 (p. 15).

`q` is the buyers' prior (p. 14), `v` the value, `c` the marginal cost (p. 5), `η` the
probability of learning one's valuation under a ban (p. 14).

**Formalization Note.** Written as printed. The expression divides by `1 − η`; the paper's
formula is undefined at `η = 1`, where Lean's convention `x / 0 = 0` makes the value `−c`.
Statements that use the threshold assume `η < 1`. -/
noncomputable def highPriceThreshold (q v c η : ℝ) : ℝ :=
  (1 - (2 - q) * η) * q * v / (1 - η) - c

end MarketplaceLeakage.Communication


