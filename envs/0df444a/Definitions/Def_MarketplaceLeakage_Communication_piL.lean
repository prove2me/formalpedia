-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_piL
-- name    : MarketplaceLeakage_Communication_piL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:10.188615+00:00
-- url     : https://prove2.me/theorems/a9755a8f-1c5f-4487-a368-a046f1129744
-- title:
--   $\Pi_L(\eta)$: profit from the low-price option under a ban
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   The marketplace's profit from the **low-price option** under a ban is
--
--   $$
--   \Pi_L(\eta)=(1-\eta+\eta q)\left(\frac{(1-(2-q)\eta)\,qv}{1-\eta}-c\right).
--   $$
--
--   It is obtained by setting the fee equal to the seller's indifference fee: the seller then sets $p_m=qv$ and sells to the $1-\eta$ uninformed buyers and to the $\eta q$ informed buyers with high value.
--
--   **Formalization Note** Written as printed. $\Pi_L$ is undefined at $\eta=1$; there Lean's $x/0=0$ gives $\Pi_L(1)=-qc$. Every statement about $\Pi_L$ alone assumes $\eta<1$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, unnumbered, p. 15 (option 2)

import Mathlib

namespace MarketplaceLeakage.Communication

/-- **`Π_L(η)`: the marketplace's profit from the low-price option under a ban.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, unnumbered, p. 15, option 2: "Set f = (1−(2−q)η)qv/(1−η) − c, which induces S to
choose the low-price option, resulting in M making a profit of
ΠL (η) = (1 − η + ηq) ((1−(2−q)η)qv/(1−η) − c)."

`q` is the buyers' prior (p. 14), `v` the value, `c` the marginal cost (p. 5), `η` the
probability of learning one's valuation under a ban (p. 14).

**Formalization Note.** Written out as printed (not through `highPriceThreshold`, so that the
formula reads as on the page). The paper's `Π_L` is undefined at `η = 1`; there Lean's
`x / 0 = 0` gives the value `q · (−c) = −qc`. Every statement about `Π_L` alone assumes
`η < 1`. -/
noncomputable def piL (q v c η : ℝ) : ℝ :=
  (1 - η + η * q) * ((1 - (2 - q) * η) * q * v / (1 - η) - c)

end MarketplaceLeakage.Communication


