-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_uniformFeeProfit
-- name    : MarketplaceLeakage_Communication_uniformFeeProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:00:27.119649+00:00
-- url     : https://prove2.me/theorems/87e0ab5b-c972-4e51-93f5-5657bb786ebb
-- title:
--   The marketplace's profit at fee $f$ with uniform switching costs, (5)
-- statement:
--   In the baseline model buyers who buy directly from the seller incur a switching cost $s$ drawn from $G$. With the uniform distribution $G(s)=s/\mu$ on $[0,\mu]$, $\mu>0$, and fees $f\le v-c$, the marketplace's profit at fee $f$ is display (5):
--
--   $$
--   \Pi(f)=\begin{cases}0 & \text{if } f\ge 2\mu,\\ f\left(1-\dfrac{f}{2\mu}\right) & \text{if } f\le 2\mu.\end{cases}
--   $$
--
--   **Formalization Note** The two branches agree at $f=2\mu$. The formula divides by $2\mu$; statements assume $\mu>0$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §4, display (5), p. 9

import Mathlib

namespace MarketplaceLeakage.Communication

/-- **The marketplace's profit at fee `f` with uniform switching costs, display (5).**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §4, display (5), p. 9: with `G(s) = s/µ` on `[0, µ]`, `µ > 0`, "The corresponding
profit for M is Π (f) = 0 if f ≥ 2µ ; f (1 − f/(2µ)) if f ≤ 2µ." (stated for fees
`f ≤ v − c`, "Assuming f ≤ v − c", p. 9).

**Formalization Note.** The two branches of (5) agree at `f = 2µ`; the first branch is used
there. The expression divides by `2µ`; statements assume `0 < µ`. -/
noncomputable def uniformFeeProfit (μ f : ℝ) : ℝ :=
  if 2 * μ ≤ f then 0 else f * (1 - f / (2 * μ))

end MarketplaceLeakage.Communication


