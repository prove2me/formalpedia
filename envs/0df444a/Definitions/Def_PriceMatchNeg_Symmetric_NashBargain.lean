-- Prove2me | Definitions.Def_PriceMatchNeg_Symmetric_NashBargain
-- name    : PriceMatchNeg_Symmetric_NashBargain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:34.761364+00:00
-- url     : https://prove2.me/theorems/e222cd8a-8de7-4a37-9f3e-65028890c5d3
-- title:
--   Generalized Nash bargaining over a price: the Nash product $u^\theta v^{1-\theta}$, individual rationality, and the bargaining solution
-- statement:
--   This file defines the generalized (asymmetric) Nash bargaining solution of a one-dimensional bargain over a price, the solution concept used for every negotiation in Shang and Cai's model.
--
--   A buyer and a seller bargain over a price $w$. If the price is $w$, the buyer earns $U(w)$ and the seller earns $V(w)$. If the negotiation fails, the buyer earns $0$ and the seller earns $d$; $(0, d)$ is the **disagreement point**. The buyer has **bargaining power** $\theta$ and the seller $1-\theta$. The **Nash product** of gains $u, v \ge 0$ is
--
--   $$N_\theta(u, v) = u^{\theta}\, v^{1-\theta}.$$
--
--   A price $w$ is **individually rational** if $w \ge 0$, $U(w) \ge 0$ and $V(w) \ge d$: neither side does worse than at the disagreement point. A price $w$ is a **Nash bargaining solution** if it is individually rational and
--
--   $$N_\theta\bigl(U(w), V(w) - d\bigr) \;\ge\; N_\theta\bigl(U(w'), V(w') - d\bigr) \quad\text{for every individually rational } w'.$$
--
--   This is the solution concept $w = \arg\max_{w} [U(w)]^{\theta}[V(w) - d]^{1-\theta}$ the paper writes for the simultaneous negotiation, the price-matching negotiation and the single-channel fallback negotiation.
--
--   **Formalization Note** The real power is Lean's `Real.rpow`, which is the ordinary real power only on non-negative bases; the Nash product is therefore only compared over the individually rational set, where both gains are non-negative. The constraint $w \ge 0$ matches the paper's feasible sets $\{w_i \ge 0\}$ (pp. 9–10).
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), pp. 7, 9–10 (PDF 7, 9–10), §2 (Nash bargaining, bargaining powers θ_i, 1 − θ_i), §3.2.1 and §3.2.2 (the arg max displays and disagreement points)

import Mathlib

namespace PriceMatchNeg.Symmetric

/-- The generalized (asymmetric) Nash product `u ^ θ * v ^ (1 - θ)` of a buyer gain `u` and a seller
gain `v`, the buyer having bargaining power `θ` and the seller `1 - θ`. It is only ever evaluated on
non-negative gains (see `IsNashBargain`), where `Real.rpow` is the ordinary real power. -/
noncomputable def nashProd (θ u v : ℝ) : ℝ := u ^ θ * v ^ (1 - θ)

/-- The individually rational prices of a one-dimensional bargain over a price `w`: `w ≥ 0`, the buyer's
payoff `U w` is at least its disagreement payoff `0`, and the seller's payoff `V w` is at least its
disagreement payoff `d`. -/
def IRFeasible (U V : ℝ → ℝ) (d w : ℝ) : Prop :=
  0 ≤ w ∧ 0 ≤ U w ∧ d ≤ V w

/-- `w` is a generalized Nash bargaining solution of the bargain over a price `w ≥ 0` between a buyer with
payoff `U`, bargaining power `θ` and disagreement payoff `0`, and a seller with payoff `V`, bargaining
power `1 - θ` and disagreement payoff `d`: `w` is individually rational and maximizes the Nash product
`(U w')^θ (V w' - d)^(1-θ)` over all individually rational prices `w'`. -/
def IsNashBargain (θ : ℝ) (U V : ℝ → ℝ) (d w : ℝ) : Prop :=
  IRFeasible U V d w ∧
    ∀ w', IRFeasible U V d w' → nashProd θ (U w') (V w' - d) ≤ nashProd θ (U w) (V w - d)

end PriceMatchNeg.Symmetric


