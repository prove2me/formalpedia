-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_piStarUniform
-- name    : MarketplaceLeakage_Communication_piStarUniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:00:44.565696+00:00
-- url     : https://prove2.me/theorems/6af737e0-b0cd-445f-af50-6b4efca2a2be
-- title:
--   $\Pi^*(\mu)$: the marketplace's equilibrium profit with uniform switching costs, (6)
-- statement:
--   With uniform switching costs $G(s)=s/\mu$ and $\bar s=\mu$, value $v$ and marginal cost $c<v$, Proposition 1 gives the marketplace's equilibrium profit, display (6):
--
--   $$
--   \Pi^*(\mu)=\begin{cases}\dfrac{\mu}{2} & \text{if } \mu\le v-c,\\ (v-c)\left(1-\dfrac{v-c}{2\mu}\right) & \text{if } \mu\ge v-c.\end{cases}
--   $$
--
--   This is the baseline profit $\Pi^*$ used in the last clause of Proposition 3.
--
--   **Formalization Note** The two branches agree at $\mu=v-c$. The formula divides by $2\mu$; statements assume $\mu>0$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, Proposition 1, display (6), p. 10

import Mathlib

namespace MarketplaceLeakage.Communication

/-- **`Π*(µ)`: the marketplace's equilibrium profit with uniform switching costs, display (6).**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), Proposition 1, display (6), p. 10: "Π∗ (µ) = µ/2 if µ ≤ v − c ;
(v − c)(1 − (v−c)/(2µ)) if µ ≥ v − c ." Here `G(s) = s/µ` and `s̄ = µ` (p. 9), `v` is the
value and `c` the marginal cost (p. 5).

**Formalization Note.** The two branches agree at `µ = v − c`; the first is used there. The
expression divides by `2µ`; statements assume `0 < µ`. That this is the maximum of (5) over
fees `f ≤ v − c` is the milestone `proof_prop_1_optimal_fee_profit`. -/
noncomputable def piStarUniform (v c μ : ℝ) : ℝ :=
  if μ ≤ v - c then μ / 2 else (v - c) * (1 - (v - c) / (2 * μ))

end MarketplaceLeakage.Communication


