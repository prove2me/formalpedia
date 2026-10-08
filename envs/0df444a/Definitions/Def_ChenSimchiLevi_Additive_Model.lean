-- Prove2me | Definitions.Def_ChenSimchiLevi_Additive_Model
-- name    : ChenSimchiLevi_Additive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:22:42.883733+00:00
-- url     : https://prove2.me/theorems/543109c4-c66f-4c18-a1d2-79870be8098c
-- title:
--   The finite-horizon pricing and inventory model of §2: demand (1), Assumptions 1–5 and the dynamic program (2)–(3)
-- statement:
--   This file sets up the finite-horizon joint pricing and inventory model of Chen and Simchi-Levi (2004, §2), in which a firm decides in each period both how much to order and what price to charge.
--
--   **Data.** There are $T$ periods $t = 1, \dots, T$. In period $t$ the demand is $w_t = \alpha_t D_t(p_t) + \beta_t$ (equation (1)), where $p_t$ is the selling price, $D_t$ is a deterministic demand function, and $\epsilon_t = (\alpha_t, \beta_t)$ is a random perturbation with law $\mu_t$ on $\mathbb R^2$. Price and expected demand $d = D_t(p)$ correspond one-to-one, and the model is written in terms of the expected demand $d$, which ranges over an interval $[\underline d_t, \bar d_t]$; the price of a decision $d$ is $P_t(d) = D_t^{-1}(d)$ and the expected revenue is $R_t(d) = d\,P_t(d)$. Ordering $y - x$ units, from inventory $x$ to level $y \ge x$, costs $k\,\delta(y - x) + c_t (y - x)$, where $k$ is a fixed cost, $c_t$ a unit cost and $\delta(u) = 1$ if $u > 0$, $\delta(u) = 0$ otherwise. Unmet demand is backlogged, and an inventory $x$ carried to the next period costs $h_t(x)$. Let
--   $$G_t(y, d) = \mathbb E\, h_t\big(y - \alpha_t d - \beta_t\big).$$
--
--   **Assumptions.** The bundle `Assumptions` collects, for every period $t = 1, \dots, T$:
--   1. (Assumption 1) $\mu_t$ is a probability measure, $\alpha_t$ and $\beta_t$ are integrable, $\mathbb E\alpha_t = 1$ and $\mathbb E\beta_t = 0$.
--   2. (Assumption 2) $\underline d_t \le \bar d_t$; $P_t$ is continuous and strictly decreasing on $[\underline d_t, \bar d_t]$; $R_t$ is concave there.
--   3. (Assumption 3) $h_t$ is convex, and for every $d \in [\underline d_t, \bar d_t]$,
--   $$\lim_{y \to +\infty} G_t(y, d) = \lim_{y \to -\infty} \big[c_t y + G_t(y, d)\big] = \lim_{y \to \infty} \big[(c_t - c_{t+1}) y + G_t(y, d)\big] = +\infty.$$
--   4. (Assumption 4) $G_t(y, d)$ is a finite expectation, $0 \le G_t(y, d)$, and $G_t(y, d) \le C_t (1 + |y|^\rho)$ for some constant $C_t$, for all $y$ and $d \in [\underline d_t, \bar d_t]$.
--   5. (Assumption 5) $\mathbb E\,|\alpha_t d + \beta_t|^\rho < \infty$ for all $d \in [\underline d_t, \bar d_t]$.
--   6. (Added) $c_{T+1} = 0$, $c_t \ge 0$ for $t = 1, \dots, T$, and $k \ge 0$.
--
--   Demand is **additive** (§3) when $\alpha_t = 1$ almost surely for every $t$, i.e. $w_t = D_t(p_t) + \beta_t$.
--
--   **Dynamic program.** For a continuation value $V$ define
--   $$g^V_t(y, d) = R_t(d) - c_t y + \mathbb E\big\{-h_t(y - \alpha_t d - \beta_t) + V(y - \alpha_t d - \beta_t)\big\},$$
--   its maximal value $G^{*V}_t(y) = \sup_{d \in [\underline d_t, \bar d_t]} g^V_t(y, d)$, and the ordering objective $-k\,\delta(y - x) + G^{*V}_t(y)$. The profit-to-go functions are $v_{T+1} \equiv 0$ and, for $t = T, \dots, 1$, (2)–(3):
--   $$v_t(x) = c_t x + \sup_{y \ge x} \Big[-k\,\delta(y - x) + g_t\big(y, d_t(y)\big)\Big], \qquad g_t = g^{v_{t+1}}_t,$$
--   where $g_t(y, d_t(y)) = G^{*v_{t+1}}_t(y)$ is the value of $g_t(y, \cdot)$ at a best expected demand $d_t(y)$. An $(s, S)$ order sends inventory $x$ to $S$ if $x < s$ and leaves it at $x$ otherwise.
--
--   These are the objects in terms of which the paper proves that, for additive demand, the profit-to-go is $k$-concave and an $(s, S, p)$ policy is optimal.
--
--   **Formalization Note.** The model is written in expected-demand space $d \in [\underline d_t, \bar d_t]$ rather than in price space; "for all $p \in [\underline p_t, \bar p_t]$" becomes "for all $d \in [\underline d_t, \bar d_t]$", which is equivalent because $D_t$ is a continuous strictly decreasing bijection between the two intervals. Independence of $\epsilon_t$ across periods is not recorded, since the dynamic program uses only each period's marginal law. Assumption 4's $O(|y|^\rho)$ is the explicit bound $C_t(1 + |y|^\rho)$ with $\rho \in \mathbb N$, uniform in $d$; this is no stronger than the pointwise bound because $G_t(y, \cdot)$ is convex in $d$. The integrability of $h_t(y - \alpha_t d - \beta_t)$ makes "$G_t$ is a finite number" explicit (a non-integrable function has Bochner integral $0$ in Lean). Assumption 5 prints $E\{D_t(p, \epsilon_t)\}^\rho < \infty$, read as the $\rho$-th absolute moment. Three hypotheses are added: $c_{T+1} = 0$ (the paper uses $c_{T+1}$ in Assumption 3 at $t = T$ without defining it, and has no salvage term), $c_t \ge 0$ (needed in the proof of Theorem 3.1(b)), and $k \ge 0$ (Definitions 2.1–2.2). The value function is defined by recursion on the number of periods to go, so that $v_{T+1} = 0$ and $v_t$ uses $c_t$, $h_t$, $\mu_t$ and $v_{t+1}$; values of the data at periods outside $1, \dots, T$ (except $c_{T+1}$) are never used. Suprema are real `sSup`, which is $0$ on unbounded sets; every theorem about them asserts that they are attained.
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), pp. 888–889, §2, (1)–(3), Assumptions 1–5; p. 889, §3 (additive demand)

import Mathlib

open MeasureTheory Filter

namespace ChenSimchiLevi.Additive

/-- `δ(u) = 1` if `u > 0` and `0` otherwise (Chen–Simchi-Levi 2004, §2, p. 888): the indicator
that an order is placed. -/
noncomputable def delta (u : ℝ) : ℝ := if 0 < u then 1 else 0

/-- The data of the finite-horizon joint pricing and inventory model of Chen–Simchi-Levi (2004),
§2, pp. 888–889, written in expected-demand space. Periods are `t = 1, …, T`; values of the
period-indexed data at other `t` are never used, except `c (T + 1)` (see `Assumptions`). -/
structure Model where
  /-- the number of periods `T` -/
  T : ℕ
  /-- the fixed ordering cost `k` (time independent) -/
  k : ℝ
  /-- the variable ordering cost `c_t` per unit -/
  c : ℕ → ℝ
  /-- the holding/backlogging cost `h_t(x)` on the inventory `x` carried to period `t + 1` -/
  h : ℕ → ℝ → ℝ
  /-- the lower end `d_t = D_t(p̄_t)` of the expected-demand range -/
  dlo : ℕ → ℝ
  /-- the upper end `d̄_t = D_t(p_t)` of the expected-demand range -/
  dhi : ℕ → ℝ
  /-- the inverse demand function `D_t⁻¹`: the price that yields expected demand `d` -/
  P : ℕ → ℝ → ℝ
  /-- the law of the random perturbation `ε_t = (α_t, β_t)` of period `t` -/
  μ : ℕ → Measure (ℝ × ℝ)
  /-- the integer `ρ` of Assumptions 4 and 5 -/
  ρ : ℕ

namespace Model

variable (M : Model)

/-- The expected revenue `R_t(d) = d D_t⁻¹(d)` of Assumption 2. -/
noncomputable def R (t : ℕ) (d : ℝ) : ℝ := d * M.P t d

/-- `G_t(y, d) = E{h_t(y - D_t(p, ε_t))}` with `D_t(p, ε_t) = α_t d + β_t` and `d = D_t(p)`
(§2, p. 888, demand (1)). -/
noncomputable def G (t : ℕ) (y d : ℝ) : ℝ :=
  ∫ ε, M.h t (y - (ε.1 * d + ε.2)) ∂(M.μ t)

/-- Assumptions 1–5 of §2 (pp. 888–889), together with the three standing hypotheses the
formalization adds: `c_{T+1} = 0`, `c_t ≥ 0` and `k ≥ 0`. -/
structure Assumptions : Prop where
  /-- Assumption 1: `ε_t` has a probability law. -/
  prob : ∀ t ∈ Finset.Icc 1 M.T, IsProbabilityMeasure (M.μ t)
  /-- Assumption 1: `α_t` is integrable with `E{α_t} = 1`. -/
  alpha_integrable : ∀ t ∈ Finset.Icc 1 M.T, Integrable (fun ε : ℝ × ℝ => ε.1) (M.μ t)
  alpha_mean : ∀ t ∈ Finset.Icc 1 M.T, ∫ ε, ε.1 ∂(M.μ t) = 1
  /-- Assumption 1: `β_t` is integrable with `E{β_t} = 0`. -/
  beta_integrable : ∀ t ∈ Finset.Icc 1 M.T, Integrable (fun ε : ℝ × ℝ => ε.2) (M.μ t)
  beta_mean : ∀ t ∈ Finset.Icc 1 M.T, ∫ ε, ε.2 ∂(M.μ t) = 0
  /-- The price range is an interval, so the expected-demand range `[d_t, d̄_t]` is one. -/
  dlo_le_dhi : ∀ t ∈ Finset.Icc 1 M.T, M.dlo t ≤ M.dhi t
  /-- Assumption 2: `D_t⁻¹` is continuous and strictly decreasing. -/
  P_continuous : ∀ t ∈ Finset.Icc 1 M.T, ContinuousOn (M.P t) (Set.Icc (M.dlo t) (M.dhi t))
  P_strictAnti : ∀ t ∈ Finset.Icc 1 M.T, StrictAntiOn (M.P t) (Set.Icc (M.dlo t) (M.dhi t))
  /-- Assumption 2: `R_t(d) = d D_t⁻¹(d)` is concave in `d`. -/
  R_concave : ∀ t ∈ Finset.Icc 1 M.T, ConcaveOn ℝ (Set.Icc (M.dlo t) (M.dhi t)) (M.R t)
  /-- Assumption 3: `h_t` is convex. -/
  h_convex : ∀ t ∈ Finset.Icc 1 M.T, ConvexOn ℝ Set.univ (M.h t)
  /-- Assumption 3: `lim_{|y| → ∞} G_t(y, d) = ∞`. -/
  G_coercive : ∀ t ∈ Finset.Icc 1 M.T, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Tendsto (fun y => M.G t y d) (cocompact ℝ) atTop
  /-- Assumption 3: `lim_{y → -∞} [c_t y + G_t(y, d)] = ∞`. -/
  G_atBot : ∀ t ∈ Finset.Icc 1 M.T, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Tendsto (fun y => M.c t * y + M.G t y d) atBot atTop
  /-- Assumption 3: `lim_{y → ∞} [(c_t - c_{t+1}) y + G_t(y, d)] = ∞`. -/
  G_atTop : ∀ t ∈ Finset.Icc 1 M.T, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Tendsto (fun y => (M.c t - M.c (t + 1)) * y + M.G t y d) atTop atTop
  /-- Assumption 4: `G_t(y, d)` is a finite expectation. -/
  h_integrable : ∀ t ∈ Finset.Icc 1 M.T, ∀ y : ℝ, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Integrable (fun ε : ℝ × ℝ => M.h t (y - (ε.1 * d + ε.2))) (M.μ t)
  /-- Assumption 4: `0 ≤ G_t(y, d)`. -/
  G_nonneg : ∀ t ∈ Finset.Icc 1 M.T, ∀ y : ℝ, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    0 ≤ M.G t y d
  /-- Assumption 4: `G_t(y, d) = O(|y|^ρ)`. -/
  G_growth : ∀ t ∈ Finset.Icc 1 M.T, ∃ C : ℝ, ∀ y : ℝ, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    M.G t y d ≤ C * (1 + |y| ^ M.ρ)
  /-- Assumption 5: `E|D_t(p, ε_t)|^ρ < ∞`. -/
  moment : ∀ t ∈ Finset.Icc 1 M.T, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
    Integrable (fun ε : ℝ × ℝ => |ε.1 * d + ε.2| ^ M.ρ) (M.μ t)
  /-- Added: no salvage cost term after the horizon, `c_{T+1} = 0`. -/
  c_terminal : M.c (M.T + 1) = 0
  /-- Added: the variable ordering cost is nonnegative. -/
  c_nonneg : ∀ t ∈ Finset.Icc 1 M.T, 0 ≤ M.c t
  /-- Added: the fixed ordering cost is nonnegative (`k ≥ 0` in Definitions 2.1–2.2). -/
  k_nonneg : 0 ≤ M.k

/-- Additive demand (§3, p. 889): `w_t = D_t(p_t) + β_t`, i.e. `α_t = 1` almost surely. -/
def IsAdditive : Prop :=
  ∀ t ∈ Finset.Icc 1 M.T, ∀ᵐ ε ∂(M.μ t), ε.1 = 1

/-- The one-period objective (3) for a continuation value `V` in place of `v_{t+1}`:
`R_t(d) - c_t y + E{-h_t(y - α_t d - β_t) + V(y - α_t d - β_t)}`. -/
noncomputable def gWith (V : ℝ → ℝ) (t : ℕ) (y d : ℝ) : ℝ :=
  M.R t d - M.c t * y +
    ∫ ε, (-M.h t (y - (ε.1 * d + ε.2)) + V (y - (ε.1 * d + ε.2))) ∂(M.μ t)

/-- `g_t(y, d_t(y))` for a continuation `V`: the supremum of `gWith V t y` over the
expected-demand range `[d_t, d̄_t]`. -/
noncomputable def GstarWith (V : ℝ → ℝ) (t : ℕ) (y : ℝ) : ℝ :=
  sSup ((M.gWith V t y) '' Set.Icc (M.dlo t) (M.dhi t))

/-- The objective of the ordering decision in (2): `-k δ(y - x) + g_t(y, d_t(y))`. -/
noncomputable def orderObjWith (V : ℝ → ℝ) (t : ℕ) (x y : ℝ) : ℝ :=
  -M.k * delta (y - x) + M.GstarWith V t y

/-- The dynamic program (2), by recursion on the number `n` of periods to go: `vAux 0 = 0` is
`v_{T+1}`, and `vAux (n + 1)` is `v_{T-n}(x) = c_{T-n} x + sup_{y ≥ x} [-k δ(y - x) + g_{T-n}(y, d_{T-n}(y))]`. -/
noncomputable def vAux (M : Model) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      M.c (M.T - n) * x + sSup ((M.orderObjWith (vAux M n) (M.T - n) x) '' Set.Ici x)

/-- The profit-to-go `v_t(x)` of (2); `v_{T+1} = 0`. -/
noncomputable def v (t : ℕ) : ℝ → ℝ := M.vAux (M.T + 1 - t)

/-- `g_t(y, d)` of (3), with continuation `v_{t+1}`. -/
noncomputable def g (t : ℕ) : ℝ → ℝ → ℝ := M.gWith (M.v (t + 1)) t

/-- `g_t(y, d_t(y))`: the value of `g_t(y, ·)` at a best expected demand. -/
noncomputable def Gstar (t : ℕ) : ℝ → ℝ := M.GstarWith (M.v (t + 1)) t

/-- The objective `-k δ(y - x) + g_t(y, d_t(y))` maximized over `y ≥ x` in (2). -/
noncomputable def orderObj (t : ℕ) : ℝ → ℝ → ℝ := M.orderObjWith (M.v (t + 1)) t

end Model

/-- The post-order inventory level of an `(s, S)` policy: order up to `S` if `x < s`, otherwise
do not order. -/
noncomputable def sSOrder (s S x : ℝ) : ℝ := if x < s then S else x

end ChenSimchiLevi.Additive


