-- Prove2me | Definitions.Def_AdaptiveBaseStock_Regret_Model
-- name    : AdaptiveBaseStock_Regret_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:36.528295+00:00
-- url     : https://prove2.me/theorems/4c0c77b2-d403-4b9e-b9f9-bfa186fc1b2d
-- title:
--   Sec. 2 — lost-sales inventory with lead time τ: i.i.d. continuous demand, inventory vector, order-up-to dynamics, period cost (1), long-run average cost
-- statement:
--   This file sets up the periodic-review, single-product lost-sales inventory system of Huh, Janakiraman, Muckstadt and Rusmevichientong (Sec. 2).
--
--   **Demand.** On a probability space $(\Omega,\mathcal F,\mathcal P)$, the demands $D_1, D_2, \dots$ are independent and identically distributed, nonnegative and integrable, with $\mu = E[D] > 0$, where $D$ denotes a generic demand. $D$ is a continuous random variable: its law has no atoms. Write $F(x) = \mathcal P[D \le x]$ for its distribution function and, for a lead time $\tau \ge 1$,
--   $$\gamma(S) = \mathcal P\left[D \le \frac{S}{\tau+1}\right].$$
--   The demand has an **infinite support** when $F(x) < 1$ for every $x$.
--
--   **Inventory vector.** An order placed in period $t$ arrives at the beginning of period $t+\tau$. The state in period $t$ is the **inventory vector**
--   $$X_t = (Q_{t-1}, Q_{t-2}, \dots, Q_{t-\tau+1}, I_t) \in \mathbb R^\tau,$$
--   made of the $\tau-1$ outstanding orders and the after-delivery on-hand inventory $I_t$. Its **inventory position** is $X_t \cdot \mathbf 1^\tau$, the on-hand stock plus everything on order, and $x \in \mathbb R^\tau_+$ means that all its entries are nonnegative.
--
--   **Order-up-to dynamics.** Under the order-up-to-$S$ policy the manager orders
--   $$Q_t(S) = [S - X_t(S)\cdot \mathbf 1^\tau]^+$$
--   before the demand $D_t$ is realized. Unmet demand is lost, and the on-hand inventory evolves as
--   $$I_{t+1} = [I_t - D_t]^+ + Q_{t-\tau+1},$$
--   the delivery $Q_{t-\tau+1}$ being the oldest outstanding order (the order just placed when $\tau = 1$). The pipeline then shifts by one period. The file allows the order-up-to level to change from period to period, which the adaptive algorithm needs.
--
--   **Costs.** With holding cost $h$ and lost-sales penalty $b$ per unit, the expected cost of a period with on-hand inventory $y$ is
--   $$C(y) = h\, E[y - D]^+ + b\, E[D - y]^+ . \qquad (1)$$
--   The **long-run average cost** of the order-up-to-$S$ policy is
--   $$C(I_\infty(S)) = \limsup_{T\to\infty} \frac1T \sum_{t=1}^T E\big[C(I_t(S))\big],$$
--   computed from the empty initial inventory vector.
--
--   **Steady state.** A probability law $\pi$ on $\mathbb R^\tau$ is a **steady-state law** of the order-up-to-$S$ chain if, from every initial inventory vector in $\mathbb R^\tau_+$, the total variation distance $\sup_B |\mathcal P[X_t(S)\in B] - \pi(B)|$ (over measurable $B$) tends to $0$.
--
--   These objects are the model on which every statement of the mission is built.
--
--   **Formalization Note** Lean period $t$ is the paper's period $t+1$, so `D t` is the paper's $D_{t+1}$ and `run … 0` is $X_1$. The pipeline is stored newest first, index $0$ being $Q_{t-1}$. The cost $C$ is a deterministic function of $y$, with the expectation taken over $D$ alone. The long-run cost is a `limsup` taken from $X_1 = 0$: the paper defines it as a limit, and Theorem 7 shows that the limit exists and does not depend on $X_1$. The steady-state law is the $X$-marginal of the paper's chain $(X_t, X_t')$, and the total variation distance is the platform definition `MarkovChainCLT.tvDist`. Nonnegativity of the demand is assumed for every sample point.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Sec. 2, pp. 5–7, eq. (1); Sec. 3.2, pp. 9–10 (γ(S), ergodicity); Sec. 5, pp. 21–22 (infinite support)

import Mathlib
import Definitions.Def_TotalVariationDist

namespace AdaptiveBaseStock.Regret

open MeasureTheory ProbabilityTheory Filter

/-- The inventory vector `X_t = (Q_{t-1}, …, Q_{t-τ+1}, I_t) ∈ ℝ^τ` (Sec. 2, p. 6).
The first component is the pipeline of the `τ - 1` outstanding orders: index `0` is the newest
order `Q_{t-1}`, index `τ - 2` is the oldest outstanding order `Q_{t-τ+1}` (the next to arrive).
The second component is the after-delivery on-hand inventory `I_t`. -/
abbrev InvVec (τ : ℕ) : Type := (Fin (τ - 1) → ℝ) × ℝ

/-- The inventory position `X_t · 1^τ` (on hand plus on order). -/
def position {τ : ℕ} (x : InvVec τ) : ℝ := x.2 + ∑ i, x.1 i

/-- `x ∈ ℝ^τ_+`: every outstanding order and the on-hand inventory are nonnegative. -/
def IsNonneg {τ : ℕ} (x : InvVec τ) : Prop := (∀ i, 0 ≤ x.1 i) ∧ 0 ≤ x.2

/-- The order of the order-up-to-`S` policy, `Q_t(S) = [S - X_t(S) · 1^τ]⁺` (p. 6). -/
noncomputable def orderQty {τ : ℕ} (S : ℝ) (x : InvVec τ) : ℝ := max (S - position x) 0

/-- The pipeline extended by the new order: index `0` is the order `Q` just placed, index `i + 1`
is the old pipeline entry `i`, and `0` beyond the pipeline. -/
noncomputable def extPipe {τ : ℕ} (Q : ℝ) (p : Fin (τ - 1) → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then Q else if h : i - 1 < τ - 1 then p ⟨i - 1, h⟩ else 0

/-- One period of the lost-sales system under order-up-to level `S` with realized demand `d`
(p. 6). The order `Q = [S - x · 1^τ]⁺` is placed before the demand; the next on-hand inventory is
`[I - d]⁺` plus the delivery `Q_{t-τ+1}` (the oldest outstanding order, or the new order itself
when `τ = 1`); the pipeline shifts by one and the new order becomes its newest entry. -/
noncomputable def step {τ : ℕ} (S d : ℝ) (x : InvVec τ) : InvVec τ :=
  (fun i => extPipe (τ := τ) (orderQty S x) x.1 i.val,
    max (x.2 - d) 0 + extPipe (τ := τ) (orderQty S x) x.1 (τ - 1))

/-- The inventory vectors under the (possibly time-varying) order-up-to levels `levels t`, from the
initial inventory vector `x₁`, along the demand path `d`. Lean period `t` is the paper's period
`t + 1`, so `run levels x₁ d 0 = x₁ = X_1` and `d t` is the paper's `D_{t+1}`. -/
noncomputable def run {τ : ℕ} (levels : ℕ → ℝ) (x₁ : InvVec τ) (d : ℕ → ℝ) : ℕ → InvVec τ
  | 0 => x₁
  | t + 1 => step (levels t) (d t) (run levels x₁ d t)

/-- The standing demand assumptions of Sec. 2 (p. 5): the demands `D 0, D 1, …` (the paper's
`D_1, D_2, …`) are independent and identically distributed, nonnegative, integrable with
`E[D] > 0`, and `D` is a continuous random variable (its law has no atoms). -/
structure IsDemandModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ) :
    Prop where
  measurable : ∀ n, Measurable (D n)
  indep : iIndepFun D P
  identDistrib : ∀ n, IdentDistrib (D n) (D 0) P P
  nonneg : ∀ n ω, 0 ≤ D n ω
  integrable : Integrable (D 0) P
  mean_pos : 0 < ∫ ω, D 0 ω ∂P
  atomless : ∀ x : ℝ, P {ω | D 0 ω = x} = 0

/-- The cumulative distribution function `F(x) = P[D ≤ x]` of the generic demand `D`. -/
noncomputable def demandCdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D₀ : Ω → ℝ)
    (x : ℝ) : ℝ :=
  P.real {ω | D₀ ω ≤ x}

/-- `γ(S) = P[D ≤ S / (τ + 1)]` (p. 10). -/
noncomputable def gammaLevel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D₀ : Ω → ℝ)
    (τ : ℕ) (S : ℝ) : ℝ :=
  demandCdf P D₀ (S / ((τ : ℝ) + 1))

/-- `D` has an infinite support: `F(x) < 1` for every `x` (the standing assumption of Sec. 5,
pp. 21–22). -/
def HasInfiniteSupport {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D₀ : Ω → ℝ) : Prop :=
  ∀ x : ℝ, demandCdf P D₀ x < 1

/-- The expected one-period cost (1), `C(y) = h · E[y - D]⁺ + b · E[D - y]⁺`, a deterministic
function of the on-hand inventory `y`. -/
noncomputable def periodCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D₀ : Ω → ℝ)
    (h b y : ℝ) : ℝ :=
  h * ∫ ω, max (y - D₀ ω) 0 ∂P + b * ∫ ω, max (D₀ ω - y) 0 ∂P

/-- The long-run average cost of the order-up-to-`S` policy,
`C(I_∞(S)) = limsup_{T → ∞} (1/T) Σ_{t=1}^T E[C(I_t(S))]`, computed from the zero initial
inventory vector (Theorem 7 shows the limit exists and does not depend on the start). -/
noncomputable def baseStockCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → ℝ) (τ : ℕ) (h b S : ℝ) : ℝ :=
  limsup (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
    ∫ ω, periodCost P (D 0) h b (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2 ∂P) atTop

/-- The law of the inventory vector `X_t(S)` in Lean period `t` under the order-up-to-`S`
policy started from `x₁`. -/
noncomputable def stateLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (τ : ℕ) (S : ℝ) (x₁ : InvVec τ) (t : ℕ) : Measure (InvVec τ) :=
  P.map (fun ω => run (fun _ => S) x₁ (fun n => D n ω) t)

/-- `π` is a steady-state law of the inventory vector under the order-up-to-`S` policy: a
probability measure such that, from every initial inventory vector in `ℝ^τ_+`, the total
variation distance between the law of `X_t(S)` and `π` tends to `0` (p. 10). -/
def IsSteadyStateLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (τ : ℕ) (S : ℝ) (π : Measure (InvVec τ)) : Prop :=
  IsProbabilityMeasure π ∧
    ∀ x₁ : InvVec τ, IsNonneg x₁ →
      Tendsto (fun t => MarkovChainCLT.tvDist (stateLaw P D τ S x₁ t) π) atTop (nhds 0)

end AdaptiveBaseStock.Regret


