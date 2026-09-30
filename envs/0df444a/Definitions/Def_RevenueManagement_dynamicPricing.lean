-- Prove2me | Definitions.Def_RevenueManagement_dynamicPricing
-- name    : RevenueManagement_dynamicPricing
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:47:48.233634+00:00
-- url     : https://prove2.me/theorems/02bbefca-f866-4436-9141-dd44b6bfebe7
-- title:
--   Dynamic pricing, Chapter 5: the Bernoulli-demand value function (5.12), the deterministic model (5.1), and the pricing-and-replenishment model (5.20) with its continuation value
-- statement:
--   The dynamic-pricing models of Chapter 5 of Talluri and van Ryzin.
--
--   **Bernoulli demand** (Sect. 5.2.2.2). In each of $T$ periods one customer arrives with a
--   random willingness to pay; offering the price $p(t, d)$, the inverse-demand function, sells
--   one unit with probability $d \in [0, 1]$, so the demand rate $d$ is the decision and
--   $r(t, d) = d\,p(t, d)$ is the revenue rate (`revenueRate`). The value function (5.12) is
--   $V_t(x) = \max_{d \in [0,1]}\{r(t, d) - d\,\Delta V_{t+1}(x)\} + V_{t+1}(x)$ with
--   $V_{T+1} = 0$, $V_t(0) = 0$ (`bernoulliValue`, `bernoulliDelta`). The **deterministic
--   model** (5.1) from period $t$ with inventory $x$ is
--   $\max \sum_{s = t}^{T} r(s, d(s))$ over rates $d(s) \in [0, 1]$ with
--   $\sum_s d(s) \le x$ (`deterministicValue`).
--
--   **Pricing with replenishment** (Sect. 5.3.2). A structure `ReplPricing` carries a probability
--   space for the demand noise, the random demand $D(t, d, \omega) = a_t(\omega)\,d + b_t(\omega)$,
--   affine in the rate (the additive and multiplicative models and their combinations), the
--   revenue rate $r(t, d)$ on $[0, \bar d]$, the unit ordering cost $c_t$, the convex
--   holding/backorder cost $h_t$ on ending inventory, and the horizon. Inventory $x$ may be
--   negative (backorders). The value function (5.20) is
--   $V_t(x) = \sup_{y \ge x,\ 0 \le d \le \bar d}\{r(t, d) - c_t(y - x) + G_{t+1}(y, d)\}$
--   with $G_{t+1}(y, d) = \mathbb E[V_{t+1}(y - D(t, d, \xi_t)) - h_t(y - D(t, d, \xi_t))]$
--   (`value`, `contValue`), $V_{T+1} = 0$. `objective t y d` is
--   $r(t, d) - c_t y + G_{t+1}(y, d)$ and `IsOptimal t x y d` says $(y, d)$ is feasible for
--   $x$ and maximizes it. `IsModel` collects the assumptions: a probability measure, bounded
--   measurable noise with $a_t \ge 0$, $r(t, \cdot)$ concave (Assumption 7.2) and continuous
--   on $[0, \bar d]$, $c_t \ge 0$, $h_t$ convex and nonnegative.
--
--   **Formalization Note** Periods are natural numbers and `value t` is the value with
--   $T + 1 - t$ periods to go; the maxima of (5.12) and (5.20) are suprema, which the
--   hypotheses make finite (a concave function is bounded on a compact interval; costs are
--   nonnegative and revenues bounded, so the objective of (5.20) is bounded above). The demand
--   is affine in the rate rather than merely convex as in Assumption 5.1: with a convex
--   non-affine demand and a non-monotone $V_{t+1} - h_t$ the joint concavity of Proposition
--   5.3 fails ($G(y, d) = -(y - d^2)^2$ at $t = T$ with $h_T(u) = u^2$). The noise has
--   bounded support, which strengthens the bounded-variance Assumption 7.6 and makes every
--   expectation a finite integral of a continuous function. The deterministic model restricts
--   rates to $[0, 1]$, the achievable rates of the Bernoulli model.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, Sect. 5.2.1 p. 189 (Eq. 5.1), Sect. 5.2.2.2 p. 203 (Eq. 5.12), Sect. 5.3.2 pp. 212-213 (Eq. 5.20 and G_{t+1}), Sect. 7.3 (Assumptions 7.2 and 7.6)

import Mathlib

open MeasureTheory

namespace RevenueManagement

/-! ### Dynamic pricing, Chapter 5 of Talluri and van Ryzin -/

/-! #### Bernoulli demand without replenishment, Sect. 5.2.2.2, and the deterministic model (5.1) -/

/-- The revenue-rate function `r(t, d) = d p(t, d)` for the inverse-demand function `p`. -/
def revenueRate (p : ℕ → ℝ → ℝ) (t : ℕ) (d : ℝ) : ℝ := d * p t d

/-- The Bernoulli-demand value function with `k` periods to go (period `t = T + 1 − k`) and `x`
units of inventory, Eq. (5.12): `V(x) = max_{d ∈ [0,1]} {r(t, d) − d ΔV'(x)} + V'(x)`, `V(0) = 0`,
`V = 0` with no period to go, where `V'` is the value with `k − 1` periods to go. -/
noncomputable def bernoulliValueGo (p : ℕ → ℝ → ℝ) (T : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | k + 1, x + 1 =>
      sSup ((fun d => revenueRate p (T - k) d -
        d * (bernoulliValueGo p T k (x + 1) - bernoulliValueGo p T k x)) '' Set.Icc (0 : ℝ) 1) +
        bernoulliValueGo p T k (x + 1)

/-- `V_t(x)` of (5.12) for `t = 1, …, T + 1`. -/
noncomputable def bernoulliValue (p : ℕ → ℝ → ℝ) (T t x : ℕ) : ℝ :=
  bernoulliValueGo p T (T + 1 - t) x

/-- `ΔV_t(x) = V_t(x) − V_t(x − 1)`, the expected marginal value of capacity. -/
noncomputable def bernoulliDelta (p : ℕ → ℝ → ℝ) (T t x : ℕ) : ℝ :=
  bernoulliValue p T t x - bernoulliValue p T t (x - 1)

/-- The deterministic dynamic-pricing model (5.1) from period `t` on with inventory `x`:
the supremum of `∑_{s=t}^{T} r(s, d(s))` over demand rates `d(s) ∈ [0, 1]` with
`∑_{s=t}^{T} d(s) ≤ x`. -/
noncomputable def deterministicValue (p : ℕ → ℝ → ℝ) (T t : ℕ) (x : ℝ) : ℝ :=
  sSup {w | ∃ d : ℕ → ℝ, (∀ s, d s ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ s ∈ Finset.Icc t T, d s ≤ x ∧
    w = ∑ s ∈ Finset.Icc t T, revenueRate p s (d s)}

/-! #### Dynamic pricing with replenishment, Sect. 5.3.2.1 -/

/-- The data of the finite-horizon pricing and replenishment model of Sect. 5.3.2: a probability
space `(Ω, P)` for the demand noise, the random demand `D(t, d, ω) = a t ω * d + b t ω` (affine in
the rate `d`, covering the additive and multiplicative models), the revenue-rate function `r`,
the unit ordering cost `c t`, the convex holding/backorder cost `h t` on ending inventory, the
largest achievable demand rate `dbar`, and the horizon `T`. -/
structure ReplPricing (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  a : ℕ → Ω → ℝ
  b : ℕ → Ω → ℝ
  r : ℕ → ℝ → ℝ
  c : ℕ → ℝ
  h : ℕ → ℝ → ℝ
  dbar : ℝ
  T : ℕ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The random demand `D(t, d, ω)`. -/
def ReplPricing.D (M : ReplPricing Ω) (t : ℕ) (d : ℝ) (ω : Ω) : ℝ := M.a t ω * d + M.b t ω

/-- The model's assumptions: `P` is a probability measure; the noise coefficients are measurable
and bounded with `a ≥ 0` (demand increasing in the rate); `r(t, ·)` is concave and continuous on
`[0, dbar]` (Assumption 7.2); ordering costs are nonnegative; `h t` is convex and nonnegative. -/
def ReplPricing.IsModel (M : ReplPricing Ω) : Prop :=
  IsProbabilityMeasure M.P ∧ 0 ≤ M.dbar ∧
  (∀ t, Measurable (M.a t) ∧ Measurable (M.b t) ∧
    ∃ K, ∀ ω, 0 ≤ M.a t ω ∧ M.a t ω ≤ K ∧ |M.b t ω| ≤ K) ∧
  (∀ t, ConcaveOn ℝ (Set.Icc 0 M.dbar) (M.r t) ∧ ContinuousOn (M.r t) (Set.Icc 0 M.dbar)) ∧
  (∀ t, 0 ≤ M.c t) ∧ (∀ t, ConvexOn ℝ Set.univ (M.h t) ∧ ∀ u, 0 ≤ M.h t u)

/-- The value function with `k` periods to go (period `t = T + 1 − k`) and inventory `x`, Eq.
(5.20): `V(x) = sup_{y ≥ x, 0 ≤ d ≤ dbar} {r(t, d) − c_t (y − x) + E[V'(y − D(t, d, ξ)) −
h_t(y − D(t, d, ξ))]}`, `V = 0` with no period to go. -/
noncomputable def ReplPricing.valueGo (M : ReplPricing Ω) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, x => sSup ((fun yd : ℝ × ℝ => M.r (M.T - k) yd.2 - M.c (M.T - k) * (yd.1 - x) +
      ∫ ω, (M.valueGo k (yd.1 - M.D (M.T - k) yd.2 ω) -
        M.h (M.T - k) (yd.1 - M.D (M.T - k) yd.2 ω)) ∂M.P) ''
      {yd | x ≤ yd.1 ∧ yd.2 ∈ Set.Icc 0 M.dbar})

/-- `V_t(x)` of (5.20) for `t = 1, …, T + 1`. -/
noncomputable def ReplPricing.value (M : ReplPricing Ω) (t : ℕ) (x : ℝ) : ℝ :=
  M.valueGo (M.T + 1 - t) x

/-- The continuation value `G_{t+1}(y, d) = E[V_{t+1}(y − D(t, d, ξ_t)) − h_t(y − D(t, d, ξ_t))]`
of period `t` for the post-order inventory `y` and demand rate `d`. -/
noncomputable def ReplPricing.contValue (M : ReplPricing Ω) (t : ℕ) (y d : ℝ) : ℝ :=
  ∫ ω, (M.value (t + 1) (y - M.D t d ω) - M.h t (y - M.D t d ω)) ∂M.P

/-- The period-`t` objective of (5.20) without the constant `c_t x`:
`r(t, d) − c_t y + G_{t+1}(y, d)`. -/
noncomputable def ReplPricing.objective (M : ReplPricing Ω) (t : ℕ) (y d : ℝ) : ℝ :=
  M.r t d - M.c t * y + M.contValue t y d

/-- `(y, d)` is an optimal order-up-to level and demand rate in period `t` with inventory `x`:
feasible (`y ≥ x`, `0 ≤ d ≤ dbar`) and maximizing the objective of (5.20). -/
def ReplPricing.IsOptimal (M : ReplPricing Ω) (t : ℕ) (x y d : ℝ) : Prop :=
  x ≤ y ∧ d ∈ Set.Icc 0 M.dbar ∧ ∀ y' d', x ≤ y' → d' ∈ Set.Icc 0 M.dbar →
    M.objective t y' d' ≤ M.objective t y d

end RevenueManagement


