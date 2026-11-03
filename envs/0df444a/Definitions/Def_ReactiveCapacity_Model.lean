-- Prove2me | Definitions.Def_ReactiveCapacity_Model
-- name    : ReactiveCapacity_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:53.396184+00:00
-- url     : https://prove2.me/theorems/7fcddb2c-88a7-4596-9460-db0d76231791
-- title:
--   Reactive-capacity model: parameters, market states, standing assumptions, cost $kq^2$ and demand
-- statement:
--   A brand-owning retailer outsources the production of a product of quality $q$ to a supplier whose unit production cost is $c=kq^2$. The market has size one, and each consumer has unit demand and utility $u=q\theta-p$ from buying at price $p$; the outside option is worth $0$. A fraction $\alpha$ of consumers has the high valuation $\theta_H$ and the rest the low valuation $\theta_L<\theta_H$.
--
--   The fraction $\alpha$ is uncertain: the market is good, $\alpha=\alpha_g$, with probability $\rho$, and bad, $\alpha=\alpha_b$, with probability $1-\rho$. The parameters are $(\theta_H,\theta_L,\alpha_g,\alpha_b,\rho,k)$.
--
--   **Standing assumptions** (pp.11, 14):
--   $$
--   0<\theta_L<\theta_H,\qquad k>0,\qquad 0<\rho<1,\qquad 0<\alpha_b,\qquad \alpha_b<\frac{\theta_L}{\theta_H}<\alpha_g,\qquad \alpha_g<1 .
--   $$
--   The middle condition is the paper's "non-trivial case" of §4: the retailer may target everybody in the bad market but only the high-valuation consumers in the good one.
--
--   **Demand.** A consumer buys when $u\ge 0$, so at quality $q\ge 0$ and price $p$ the demand in a market with high-valuation fraction $\alpha$ is
--   $$
--   D(q,\alpha,p)=(1-\alpha)\,\mathbf 1[p\le q\theta_L]+\alpha\,\mathbf 1[p\le q\theta_H]
--   =\begin{cases}1 & p\le q\theta_L,\\ \alpha & q\theta_L<p\le q\theta_H,\\ 0 & p>q\theta_H.\end{cases}
--   $$
--
--   These are the primitives of the game on which every statement of the mission is made.
--
--   **Formalization Note** The reactive capacity $\bar Q$ is not a parameter field: it varies in the results and is a separate argument. The ratio conditions are written without division ($\alpha_b\theta_H<\theta_L<\alpha_g\theta_H$). Indifferent consumers buy, as in the paper's prices $p=q\theta_H$ and $p=q\theta_L$.
-- source:
--   Jiang–Tian, Effects of Reactive Capacity on Product Quality and Firm Profitability in an Uncertain Market, SSRN 3308215 (version of May 5, 2022), §3, pp.11–13 (PDF 11–13); non-trivial case αb < θL/θH < αg, §4, p.14 (PDF 14)

import Mathlib

namespace ReactiveCapacity

/-- The parameters `(θ_H, θ_L, α_g, α_b, ρ, k)` of the reactive-capacity model.
B. Jiang, L. Tian, *Effects of Reactive Capacity on Product Quality and Firm Profitability in an
Uncertain Market*, SSRN 3308215 (version of May 5, 2022), §3, pp.11–13 (PDF 11–13).

* `θH`, `θL` are the high and low willingness to pay for quality (p.11);
* `αg`, `αb` are the fraction of high-valuation consumers in the good and the bad market (p.11);
* `ρ` is the probability of the good market (p.11);
* `k` is the cost coefficient: the supplier's unit cost of quality `q` is `c = k q²` (p.11).

**Formalization Note** The reactive capacity `Q̄` is not a field: it varies in the results, so it is
a separate argument of every game-theoretic object. The fields are bare reals; the paper's standing
assumptions are the separate predicate `Params.Standing`. -/
structure Params where
  θH : ℝ
  θL : ℝ
  αg : ℝ
  αb : ℝ
  ρ : ℝ
  k : ℝ

/-- The two market states: good (`α = α_g`, probability `ρ`) and bad (`α = α_b`, probability
`1 − ρ`), p.11. -/
inductive State
  | good
  | bad
  deriving DecidableEq

/-- The fraction `α` of high-valuation consumers in a market state (p.11). -/
def Params.alpha (P : Params) : State → ℝ
  | .good => P.αg
  | .bad => P.αb

/-- The probability of a market state: `ρ` for the good market, `1 − ρ` for the bad one (p.11). -/
def Params.prob (P : Params) : State → ℝ
  | .good => P.ρ
  | .bad => 1 - P.ρ

/-- The standing assumptions of §3–§4 (pp.11, 14): `0 < θ_L < θ_H` (p.11), `k > 0` (p.11),
`ρ ∈ (0,1)` (p.11), `α ∈ (0,1)` with `α_b < α_g` (p.11), and the non-trivial case of §4,
`α_b < θ_L/θ_H < α_g` (p.14).

**Formalization Note** The ratio conditions are written without division, as
`α_b θ_H < θ_L` and `θ_L < α_g θ_H`; with `θ_H > 0` they are the paper's. Together with
`α_b > 0` and `α_g < 1` they give `0 < α_b < α_g < 1`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.θL ∧ P.θL < P.θH ∧ 0 < P.k ∧ 0 < P.ρ ∧ P.ρ < 1 ∧ 0 < P.αb ∧
    P.αb * P.θH < P.θL ∧ P.θL < P.αg * P.θH ∧ P.αg < 1

/-- The supplier's unit production cost `c = k q²` for quality `q` (p.11). -/
def Params.cost (P : Params) (q : ℝ) : ℝ := P.k * q ^ 2

/-- Demand at quality `q` and retail price `p` in a market whose high-valuation fraction is `α`
(p.11). The market has size one; a consumer of type `θ` has unit demand and utility `u = qθ − p`,
and buys when `u ≥ 0` (the outside option is worth `0`). A fraction `α` has `θ = θ_H` and the rest
`θ = θ_L`, so the demand is `(1 − α)·[p ≤ qθ_L] + α·[p ≤ qθ_H]`: for `q ≥ 0` it is `1` when
`p ≤ qθ_L`, `α` when `qθ_L < p ≤ qθ_H`, and `0` otherwise.

**Formalization Note** Indifferent consumers (`u = 0`) buy, as in the paper's prices `p = qθ_H`
and `p = qθ_L` (Tables B and C). -/
noncomputable def Params.demand (P : Params) (q α p : ℝ) : ℝ :=
  (if p ≤ q * P.θL then 1 - α else 0) + (if p ≤ q * P.θH then α else 0)

end ReactiveCapacity


