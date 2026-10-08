-- Prove2me | Definitions.Def_ChenBullwhip_Decentralized_Chain
-- name    : ChenBullwhip_Decentralized_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:21:07.40776+00:00
-- url     : https://prove2.me/theorems/9136ed21-b019-4359-9f00-cab7e3451426
-- title:
--   The decentralized multistage chain: forecasts $\hat D^{(k)}_t$, order-up-to points $y^k_t = L_k\hat D^{(k)}_t$, orders $q^k_t$
-- statement:
--   Fix an i.i.d. symmetric demand process $D_t = \mu + \epsilon_t$, a number $p \ge 1$ of observations, and lead times $L_1, L_2, \dots \in \mathbb N$, where $L_k$ is the lead time between stages $k$ and $k+1$. In the **decentralized** serial chain of §3 of Chen, Drezner, Ryan and Simchi-Levi (2000), the retailer (stage 1) shares no customer demand information, and each stage forecasts from the orders of the stage below it. Stage $k$ uses the forecast
--
--   $$\hat D^{(1)}_t = \frac{\sum_{i=1}^{p} D_{t-i}}{p}, \qquad \hat D^{(k)}_t = \frac{\sum_{j=0}^{p-1} q^{k-1}_{t-j}}{p} \quad (k \ge 2),$$
--
--   and the order-up-to point $y^k_t = L_k\,\hat D^{(k)}_t$ (policy (2) with $z = 0$). Its orders are
--
--   $$q^1_t = y^1_t - y^1_{t-1} + D_{t-1}, \qquad q^k_t = y^k_t - y^k_{t-1} + q^{k-1}_t \quad (k \ge 2).$$
--
--   Stage $k$ receives $q^{k-1}_t$ at the end of period $t-1$ (no information lead time), updates its order-up-to point to $y^k_t$ and orders $q^k_t$ so as to raise its inventory position to $y^k_t$. Orders may be negative (excess inventory is returned without cost).
--
--   **Formalization Note** The paper does not print the formula for $q^k_t$. It is the §2.2 identity $q_t = y_t - y_{t-1} + D_{t-1}$ applied to a stage whose incoming demand is $q^{k-1}_t$, as the sequence of events on p. 440 describes (stage $k$ "receives the order $q^{k-1}_t$ … and immediately place[s] an order … to raise his inventory to level $y^k_t$"). The orders are defined by recursion on $k$ with the convention $q^0_t := D_{t-1}$, so stage 1's recursion is exactly §2.2's. Stage 1's forecast is the printed $\sum_{i=1}^p D_{t-i}/p$ and stage $k \ge 2$'s is the printed $\sum_{j=0}^{p-1} q^{k-1}_{t-j}/p$. The index $0$ is a convention only; the theorems concern stages $k \ge 1$.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 441, Theorem 3.2 (forecasts and policy) and the paragraph before it; p. 440, sequence of events; p. 437, §2.2 (order identity)

import Mathlib
import Definitions.Def_ChenBullwhip_Decentralized_IIDDemand

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Decentralized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The forecast `D̂^{(k)}ₜ` of stage `k` of the decentralized chain (Theorem 3.2), given the
order stream `prev` of the previous stage: stage `1` averages the customer demands,
`D̂^{(1)}ₜ = (∑_{i=1}^p D_{t-i}) / p`, and a stage `k ≥ 2` averages the orders it received,
`D̂^{(k)}ₜ = (∑_{j=0}^{p-1} q^{k-1}_{t-j}) / p` (here `prev = q^{k-1}`). -/
noncomputable def IIDDemand.stageForecast (X : IIDDemand P) (p k : ℕ) (prev : ℤ → Ω → ℝ)
    (t : ℤ) (ω : Ω) : ℝ :=
  if k = 1 then (∑ i ∈ Finset.Icc 1 p, X.D (t - i) ω) / p
  else (∑ j ∈ Finset.range p, prev (t - j) ω) / p

/-- The orders of the decentralized chain. `stageOrder X p L k t` is `q^k_t`, the order placed
by stage `k ≥ 1` in period `t`, when every stage `k` uses the order-up-to point
`y^k_t = L_k D̂^{(k)}_t` (no safety stock) and orders `q^k_t = y^k_t − y^k_{t-1} + q^{k-1}_t`,
raising its inventory position to `y^k_t` after receiving the downstream order `q^{k-1}_t`.
The index `k = 0` is the convention `q^0_t = D_{t-1}`, the customer demand the retailer
(stage 1) replenishes, so that stage 1 orders `q^1_t = y^1_t − y^1_{t-1} + D_{t-1}` as in §2.2. -/
noncomputable def IIDDemand.stageOrder (X : IIDDemand P) (p : ℕ) (L : ℕ → ℕ) :
    ℕ → ℤ → Ω → ℝ
  | 0 => fun t ω => X.D (t - 1) ω
  | k + 1 => fun t ω =>
      (L (k + 1) : ℝ) * X.stageForecast p (k + 1) (X.stageOrder p L k) t ω
        - (L (k + 1) : ℝ) * X.stageForecast p (k + 1) (X.stageOrder p L k) (t - 1) ω
        + X.stageOrder p L k t ω

/-- The order-up-to point of stage `k ≥ 1`: `y^k_t = L_k D̂^{(k)}_t`.
Stage `0` is only a recursion convention and has order-up-to point `0`. -/
noncomputable def IIDDemand.stageOrderUpTo (X : IIDDemand P) (p : ℕ) (L : ℕ → ℕ) :
    ℕ → ℤ → Ω → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun t ω =>
      (L (k + 1) : ℝ) * X.stageForecast p (k + 1) (X.stageOrder p L k) t ω

/-- The order recursion in terms of the order-up-to points:
`q^k_t = y^k_t − y^k_{t-1} + q^{k-1}_t` for `k ≥ 1`. -/
theorem IIDDemand.stageOrder_succ (X : IIDDemand P) (p : ℕ) (L : ℕ → ℕ) (k : ℕ) (t : ℤ)
    (ω : Ω) :
    X.stageOrder p L (k + 1) t ω =
      X.stageOrderUpTo p L (k + 1) t ω - X.stageOrderUpTo p L (k + 1) (t - 1) ω
        + X.stageOrder p L k t ω := rfl

end ChenBullwhip.Decentralized


