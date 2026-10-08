-- Prove2me | Definitions.Def_ChenBullwhip_Decentralized_SingleStage
-- name    : ChenBullwhip_Decentralized_SingleStage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:21:01.020726+00:00
-- url     : https://prove2.me/theorems/dc63954c-ef1a-4aeb-94ae-aa61b570d2f1
-- title:
--   Single-stage moving-average order-up-to policy, Eqs. (2)–(3), and the order $q_t$
-- statement:
--   Fix an i.i.d. symmetric demand process $D_t = \mu + \epsilon_t$, a number $p \ge 1$ of observations, a lead time $L \in \mathbb N$, a safety factor $z \in \mathbb R$ and a constant $C = C_{L,\rho} \in \mathbb R$. The retailer of §2 of Chen, Drezner, Ryan and Simchi-Levi (2000) estimates the lead-time demand and the standard deviation of the $L$-period forecast error by moving averages over the last $p$ periods (Eq. (3)):
--
--   $$\hat D^L_t = L\,\frac{\sum_{i=1}^p D_{t-i}}{p}, \qquad \hat\sigma^L_{et} = C_{L,\rho}\sqrt{\frac{\sum_{i=1}^p (e_{t-i})^2}{p}},$$
--
--   where $e_t = D_t - \hat D^1_t$ is the one-period forecast error. The order-up-to point is (Eq. (2))
--
--   $$y_t = \hat D^L_t + z\,\hat\sigma^L_{et},$$
--
--   and the order placed in period $t$ is (§2.2)
--
--   $$q_t = y_t - y_{t-1} + D_{t-1}.$$
--
--   The order may be negative: excess inventory is returned without cost. This object is the single-stage order process whose variance Eq. (6) bounds; with $z = 0$ and $L = L_1$ it coincides with the orders of stage 1 of the decentralized chain.
--
--   **Formalization Note** The paper calls $C_{L,\rho}$ "a constant function of $L$, $\rho$ and $p$" without fixing it; it is a free real parameter $C$. The names are `leadTimeForecast` ($\hat D^L_t$), `forecastError` ($e_t$), `sigmaHat` ($\hat\sigma^L_{et}$), `orderUpTo` ($y_t$) and `order` ($q_t$).
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 437, Eqs. (2)–(3) and §2.2 (q_t = y_t − y_{t−1} + D_{t−1})

import Mathlib
import Definitions.Def_ChenBullwhip_Decentralized_IIDDemand

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Decentralized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The moving-average estimate of the lead-time demand, Eq. (3):
`D̂ᴸₜ = L (∑_{i=1}^p D_{t-i}) / p`. -/
noncomputable def IIDDemand.leadTimeForecast (X : IIDDemand P) (L p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  (L : ℝ) * ((∑ i ∈ Finset.Icc 1 p, X.D (t - i) ω) / p)

/-- The one-period forecast error `eₜ = Dₜ − D̂¹ₜ`. -/
noncomputable def IIDDemand.forecastError (X : IIDDemand P) (p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.D t ω - X.leadTimeForecast 1 p t ω

/-- The estimate of the standard deviation of the `L`-period forecast error, Eq. (3):
`σ̂ᴸₑₜ = C √(∑_{i=1}^p (e_{t-i})² / p)`, where the paper's constant `C_{L,ρ}` is the free real
parameter `C`. -/
noncomputable def IIDDemand.sigmaHat (X : IIDDemand P) (C : ℝ) (p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 p, (X.forecastError p (t - i) ω) ^ 2) / p)

/-- The order-up-to point of the single-stage policy, Eq. (2): `yₜ = D̂ᴸₜ + z σ̂ᴸₑₜ`. -/
noncomputable def IIDDemand.orderUpTo (X : IIDDemand P) (C z : ℝ) (L p : ℕ) (t : ℤ) (ω : Ω) :
    ℝ :=
  X.leadTimeForecast L p t ω + z * X.sigmaHat C p t ω

/-- The order placed by the retailer in period `t` (§2.2): `qₜ = yₜ − yₜ₋₁ + Dₜ₋₁`. It may be
negative (excess inventory is returned without cost). -/
noncomputable def IIDDemand.order (X : IIDDemand P) (C z : ℝ) (L p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.orderUpTo C z L p t ω - X.orderUpTo C z L p (t - 1) ω + X.D (t - 1) ω

end ChenBullwhip.Decentralized


