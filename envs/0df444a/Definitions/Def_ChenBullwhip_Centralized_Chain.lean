-- Prove2me | Definitions.Def_ChenBullwhip_Centralized_Chain
-- name    : ChenBullwhip_Centralized_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:33:11.685742+00:00
-- url     : https://prove2.me/theorems/922f8f68-7a8b-4c27-b1f2-dacd9b14eeca
-- title:
--   Multistage supply chain with centralized demand information: stage order-up-to points and orders, §3
-- statement:
--   Consider a serial supply chain whose stages are numbered $k = 1, 2, \dots$, stage $1$ being the retailer. Every stage sees the customer demands $(D_t)$ and uses the same moving average with $p$ observations, $\hat D_t = \sum_{i=1}^p D_{t-i}/p$. Stage $k$ has lead time $L_k \in \mathbb N$ (between stages $k$ and $k+1$) and safety factor $z_k \in \mathbb R$, and its order-up-to point in period $t$ is
--
--   $$y^k_t = L_k \hat D_t + z_k \hat\sigma^{L_k}_{et}, \qquad \hat\sigma^{L_k}_{et} = C_{L_k,\rho}\sqrt{\frac{\sum_{i=1}^p (e_{t-i})^2}{p}},$$
--
--   which is the retailer's order-up-to point of Eq. (2) with lead time $L_k$ and safety factor $z_k$.
--
--   The orders follow the paper's sequence of events. At the end of period $t-1$ the retailer observes $D_{t-1}$ and orders $q^1_t$ to raise his inventory to $y^1_t$; stage $k \ge 2$ receives the order $q^{k-1}_t$ together with $D_{t-1}$ and immediately orders $q^k_t$ to raise its inventory to $y^k_t$. Accordingly
--
--   $$q^1_t = y^1_t - y^1_{t-1} + D_{t-1}, \qquad q^k_t = y^k_t - y^k_{t-1} + q^{k-1}_t \quad (k \ge 2).$$
--
--   Stage $1$'s order is exactly the single-stage order $q_t$ of §2.2 with $L = L_1$ and $z = z_1$. These orders are the subject of Theorem 3.1.
--
--   **Formalization Note** The paper does not print a formula for $q^k_t$; the recursion is read from the sequence of events on pp. 440–441, by the same reasoning that gives $q_t = y_t - y_{t-1} + D_{t-1}$ in §2.2: a stage whose order-up-to point moves from $y^k_{t-1}$ to $y^k_t$ while it ships the incoming order $q^{k-1}_t$ must order $y^k_t - y^k_{t-1} + q^{k-1}_t$. In Lean the recursion starts from the convention $q^0_t = D_{t-1}$, the customer demand seen at the end of period $t-1$. The lead times are a sequence $L : \mathbb N \to \mathbb N$, the safety factors a sequence $z : \mathbb N \to \mathbb R$, and the unspecified constants $C_{L_k,\rho}$ are $C(L_k)$ for an arbitrary function $C : \mathbb N \to \mathbb R$ (so two stages with the same lead time share the constant, as in the paper, where $\rho$ and $p$ are common to all stages).
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), pp. 440–441, §3 (the order-up-to point y^k_t and the sequence of events)

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Centralized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- p. 440, §3: the order-up-to point of stage `k` with centralized demand information,
`yᵏₜ = L_k D̂ₜ + z_k σ̂^{L_k}_{et}`, where `D̂ₜ = ∑_{i=1}^p D_{t-i}/p` and
`σ̂^{L_k}_{et} = C_{L_k,ρ} √(∑_{i=1}^p (e_{t-i})²/p)`. Stage `k` has lead time `L k` and safety
factor `z k`; the unspecified constant `C_{L_k,ρ}` is `C (L k)`. It is the §2 order-up-to point
with lead time `L k`. -/
noncomputable def AR1Demand.chainLevel (X : AR1Demand P) (p : ℕ) (L : ℕ → ℕ) (C z : ℕ → ℝ)
    (k : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.orderUpTo (C (L k)) (z k) (L k) p t ω

/-- pp. 440–441, §3 (sequence of events): the order `qᵏₜ` placed by stage `k` in period `t`.
Stage 1 orders `q¹ₜ = y¹ₜ - y¹_{t-1} + D_{t-1}`; stage `k ≥ 2` receives the order `q^{k-1}_t`
and orders `qᵏₜ = yᵏₜ - yᵏ_{t-1} + q^{k-1}_t`. The value at `k = 0` is the convention
`q⁰ₜ = D_{t-1}` (the customer demand seen at the end of period `t - 1`); stages are numbered from 1. -/
noncomputable def AR1Demand.chainOrder (X : AR1Demand P) (p : ℕ) (L : ℕ → ℕ) (C z : ℕ → ℝ) :
    ℕ → ℤ → Ω → ℝ
  | 0, t, ω => X.D (t - 1) ω
  | k + 1, t, ω =>
      X.chainLevel p L C z (k + 1) t ω - X.chainLevel p L C z (k + 1) (t - 1) ω
        + X.chainOrder p L C z k t ω

end ChenBullwhip.Centralized


