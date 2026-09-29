-- Prove2me | Definitions.Def_LiuVanRyzin_PowerModel
-- name    : LiuVanRyzin_PowerModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:35:47.877355+00:00
-- url     : https://prove2.me/theorems/ffc4ae8e-2da6-4755-9cd2-151927b89af8
-- title:
--   Fill rate, capacity, profit $\Pi(v)$, first-order condition (7) and $U_c$ of (8) in the power–uniform model
-- statement:
--   From §3 on, Liu and van Ryzin (2008) take valuations uniform on $[0,\bar U]$ and the power utility $u(x)=x^\gamma$ with $0<\gamma<1$. Let $N>0$ be the market size, $p_1>p_2$ the two prices and $\alpha<p_2$ the unit cost. For a cutoff valuation $v$ with $p_1\le v\le\bar U$ the module defines:
--
--   1. the **fill rate** that makes $v$ the indifferent valuation (Eq. (2) with $u=x^\gamma$),
--   $$q(v)=\left(\frac{v-p_1}{v-p_2}\right)^\gamma;$$
--   2. the **capacity** that produces this fill rate, solved from the constraint of (5),
--   $$C(v)=\frac{N}{\bar U}\bigl(\bar U - v + (v-p_2)\,q(v)\bigr);$$
--   3. the **segmented-market profit** of Eq. (6),
--   $$\Pi(v)=\frac{N}{\bar U}\left((p_1-\alpha)(\bar U-v)+(p_2-\alpha)(v-p_2)\left(\frac{v-p_1}{v-p_2}\right)^\gamma\right);$$
--   4. the **low-price-only profit** $\Pi^{NS}=(p_2-\alpha)N\bar F(p_2)=(p_2-\alpha)\frac{N}{\bar U}(\bar U-p_2)$;
--   5. the left-hand side of the **first-order condition** (7),
--   $$\left(\frac{v-p_1}{v-p_2}\right)^\gamma\left(1+\frac{\gamma(p_1-p_2)}{v-p_1}\right)-\frac{p_1-\alpha}{p_2-\alpha};$$
--   6. the **critical valuation bound** (8), as a function of a value $v^0$,
--   $$U_c=\frac{(p_2+\gamma(p_1-\alpha))v^0-p_2(p_1+\gamma(p_2-\alpha))}{v^0-p_1+\gamma(p_1-p_2)}.$$
--
--   These are the closed forms in which Lemma 1 and Proposition 3 are stated; $q^0=q(v^0)$ and $C^0=C(v^0)$ are the optimal fill rate and stocking quantity of the rationing solution.
--
--   **Formalization Note** The power is `Real.rpow`, which for a negative base is not the paper's quantity; every statement using these definitions stays on $v\ge p_1$ (or $v>p_1$ where $(v-p_1)^{-1}$ appears). At $v=p_1$ the fill rate is $0^\gamma=0$. $\Pi(v)$ is written directly as in (6); it equals the objective of (5), $\frac N{\bar U}(p_1-p_2)(\bar U-v)+(p_2-\alpha)C(v)$, by algebra. Division by zero returns $0$ in Lean; the mission's hypotheses ($\bar U>0$, $v>p_1$, $\alpha<p_2$) keep every denominator nonzero.
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), pp. 1121–1122, §2.2 (Π^NS), §3 (uniform law, power utility), §3.1 Eqs. (5)–(8)

import Mathlib

namespace LiuVanRyzin

/-- The fill rate as a function of the cutoff `v` under the power utility `u(x) = x ^ γ`
(§3.1, constraint of Eq. (5), from Eq. (2)): `q(v) = ((v - p₁) / (v - p₂)) ^ γ`, meaningful for
`v ≥ p₁ > p₂`. -/
noncomputable def fillRate (p₁ p₂ γ v : ℝ) : ℝ :=
  ((v - p₁) / (v - p₂)) ^ γ

/-- The stocking quantity `C` that induces cutoff `v`, solved from the constraint of Eq. (5)
(§3.1, p. 1122; `C⁰` of Proposition 3): `C(v) = (N / Ū) (Ū - v + (v - p₂) q(v))`. -/
noncomputable def capacity (N Ubar p₁ p₂ γ v : ℝ) : ℝ :=
  (N / Ubar) * (Ubar - v + (v - p₂) * fillRate p₁ p₂ γ v)

/-- The segmented-market profit `Π(v)` of Eq. (6), §3.1, p. 1122:
`Π(v) = (N / Ū) ((p₁ - α)(Ū - v) + (p₂ - α)(v - p₂) ((v - p₁)/(v - p₂)) ^ γ)`. -/
noncomputable def segProfit (N Ubar p₁ p₂ α γ v : ℝ) : ℝ :=
  (N / Ubar) * ((p₁ - α) * (Ubar - v) + (p₂ - α) * (v - p₂) * fillRate p₁ p₂ γ v)

/-- The profit of serving the entire market at the low price only, `Π^NS = (p₂ - α) N F̄(p₂)`
(§2.2, p. 1121), with the uniform law on `[0, Ū]` of §3: `F̄(p₂) = (Ū - p₂) / Ū`. -/
noncomputable def lowPriceProfit (N Ubar p₂ α : ℝ) : ℝ :=
  (p₂ - α) * (N / Ubar) * (Ubar - p₂)

/-- The left-hand side of the first-order condition, Eq. (7), §3.1, p. 1122:
`((v - p₁)/(v - p₂)) ^ γ (1 + γ (p₁ - p₂)/(v - p₁)) - (p₁ - α)/(p₂ - α)`. -/
noncomputable def focLHS (p₁ p₂ α γ v : ℝ) : ℝ :=
  fillRate p₁ p₂ γ v * (1 + γ * (p₁ - p₂) / (v - p₁)) - (p₁ - α) / (p₂ - α)

/-- The critical valuation bound `U_c` of Eq. (8), §3.1, p. 1122, as a function of the root
`v⁰` of Eq. (7):
`U_c = ((p₂ + γ(p₁ - α)) v⁰ - p₂ (p₁ + γ(p₂ - α))) / (v⁰ - p₁ + γ(p₁ - p₂))`. -/
noncomputable def criticalU (p₁ p₂ α γ v₀ : ℝ) : ℝ :=
  ((p₂ + γ * (p₁ - α)) * v₀ - p₂ * (p₁ + γ * (p₂ - α))) / (v₀ - p₁ + γ * (p₁ - p₂))

end LiuVanRyzin


