-- Prove2me | Definitions.Def_GravesIMA_Stages_Model
-- name    : GravesIMA_Stages_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:18.780148+00:00
-- url     : https://prove2.me/theorems/94e7eb38-b6ec-495c-aab6-9fdb3b45ff5d
-- title:
--   §2–§3, pp. 51–57 — IMA(0,1,1) demand (1), EWMA forecasts (3)/(11), adaptive base-stock orders (7)/(15), inventory balance (6)/(14)
-- statement:
--   This file sets up the single-item inventory model of Graves (1999) for one stage and for two stages in series. Time is indexed by the integers $t\in\mathbb Z$; periods of operation are $t=1,2,\dots$.
--
--   1. **One stage** (`IsStage μ a L e d F q x`, §2, pp. 51–52). Given a mean level $\mu$, a parameter $a$, a lead time $L\in\mathbb N$ and shocks $e_t$, the demand $d$ is the integrated moving average process
--   $$d_1=\mu+e_1,\qquad d_t=d_{t-1}-(1-a)e_{t-1}+e_t\quad(t\ge2),\tag{1}$$
--   the forecast $F$ is the exponentially weighted moving average
--   $$F_1=\mu,\qquad F_{t+1}=a\,d_t+(1-a)F_t\quad(t\ge1),\tag{3}$$
--   the orders follow the adaptive base-stock policy, with $q_t=\mu$ for $t\le0$ and
--   $$q_t=d_t+L(F_{t+1}-F_t)\quad(t\ge1),\tag{7}$$
--   and the inventory (negative values are backorders) obeys the balance equation
--   $$x_t=x_{t-1}-d_t+q_{t-L}\quad(t\ge1).\tag{6}$$
--   The initial inventory $x_0$ is not constrained, and orders may be negative.
--
--   2. **Upstream stage** (`IsUpstream μ b K q G p y`, §3, pp. 55–57). It sees the downstream orders $q$ as its demand, has lead time $K\in\mathbb N$ and parameter $b$:
--   $$G_1=\mu,\quad G_{t+1}=b\,q_t+(1-b)G_t\ (t\ge1),\tag{11}$$
--   $p_t=\mu$ for $t\le0$, $p_t=q_t+K(G_{t+1}-G_t)$ for $t\ge1$ (15), and $y_t=y_{t-1}-q_t+p_{t-K}$ for $t\ge1$ (14), with $y_0$ free.
--
--   3. **The upstream smoothing constant** `upBeta α L` is $\beta=\alpha/(1+L\alpha)$ (p. 55).
--
--   4. **The two-stage system** `IsTwoStage μ α L K ε d F q x G p y` is the conjunction of the downstream stage with parameters $(\mu,\alpha,L)$ and shocks $\varepsilon$ and the upstream stage with parameters $(\mu,\beta,K)$ fed by the downstream orders $q$.
--
--   5. **Masked shocks** `masked e` is the sequence equal to $e_s$ for $s\ge1$ and to $0$ for $s\le0$; it implements the paper's convention "$\varepsilon_t=0$ for $t\le0$" in P1 and P2.
--
--   These are the paper's objects as defined by their recursions; none of the closed forms (2), (5), (9), (10), P1 or P2 is built into them, so those remain theorems.
--
--   **Formalization Note** The model is a predicate on sequences $\mathbb Z\to\mathbb R$ rather than a construction, so every theorem quantifies over all sequences satisfying it. The stage predicate is generic in the parameter and the shocks so that it can also describe the upstream stage once that stage's demand is shown to be IMA(0,1,1); the upstream predicate is defined separately, from (11), (14), (15) alone. The restriction $0\le\alpha\le1$ and the normality of the shocks are hypotheses of the theorems, not part of these definitions.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), pp. 51–52, §2, (1), (3), (6), (7); pp. 55–57, §3, (11), (14), (15), β = α/(1 + Lα)

import Mathlib

namespace GravesIMA.Stages

/-- One inventory stage under the adaptive base-stock policy (Graves 1999, §2, pp. 51–52).
Time is `ℤ`; the model clauses hold for periods `t ≥ 1` (for `t ≥ 2` in the recursion (1)),
the order boundary condition for `t ≤ 0`.
* demand `d` is IMA(0,1,1) with mean level `μ`, smoothing/inertia parameter `a` and shocks `e`:
  `d 1 = μ + e 1`, `d t = d (t-1) - (1 - a) e (t-1) + e t` for `t ≥ 2`             — (1);
* `F` is the exponentially weighted moving-average forecast:
  `F 1 = μ`, `F (t+1) = a d t + (1 - a) F t` for `t ≥ 1`                           — (3);
* `q` are the orders: `q t = μ` for `t ≤ 0`, `q t = d t + L (F (t+1) - F t)` for `t ≥ 1` — (7);
* `x` is the inventory: `x t = x (t-1) - d t + q (t - L)` for `t ≥ 1`              — (6).
The initial inventory `x 0` is left free; negative orders are permitted. -/
def IsStage (μ a : ℝ) (L : ℕ) (e d F q x : ℤ → ℝ) : Prop :=
  d 1 = μ + e 1 ∧
  (∀ t : ℤ, 2 ≤ t → d t = d (t - 1) - (1 - a) * e (t - 1) + e t) ∧
  F 1 = μ ∧
  (∀ t : ℤ, 1 ≤ t → F (t + 1) = a * d t + (1 - a) * F t) ∧
  (∀ t : ℤ, t ≤ 0 → q t = μ) ∧
  (∀ t : ℤ, 1 ≤ t → q t = d t + (L : ℝ) * (F (t + 1) - F t)) ∧
  (∀ t : ℤ, 1 ≤ t → x t = x (t - 1) - d t + q (t - (L : ℤ)))

/-- The upstream stage (Graves 1999, §3, pp. 55–57). It sees the downstream orders `q` as its
demand, has lead time `K` and smoothing parameter `b`.
* `G` is its forecast: `G 1 = μ`, `G (t+1) = b q t + (1 - b) G t` for `t ≥ 1`           — (11);
* `p` are its orders: `p t = μ` for `t ≤ 0`, `p t = q t + K (G (t+1) - G t)` for `t ≥ 1` — (15);
* `y` is its inventory: `y t = y (t-1) - q t + p (t - K)` for `t ≥ 1`                   — (14).
The initial inventory `y 0` is left free; negative orders are permitted. -/
def IsUpstream (μ b : ℝ) (K : ℕ) (q G p y : ℤ → ℝ) : Prop :=
  G 1 = μ ∧
  (∀ t : ℤ, 1 ≤ t → G (t + 1) = b * q t + (1 - b) * G t) ∧
  (∀ t : ℤ, t ≤ 0 → p t = μ) ∧
  (∀ t : ℤ, 1 ≤ t → p t = q t + (K : ℝ) * (G (t + 1) - G t)) ∧
  (∀ t : ℤ, 1 ≤ t → y t = y (t - 1) - q t + p (t - (K : ℤ)))

/-- `β = α / (1 + L α)`, the smoothing parameter of the upstream forecast (p. 55). -/
noncomputable def upBeta (α : ℝ) (L : ℕ) : ℝ := α / (1 + (L : ℝ) * α)

/-- The two-stage serial system of §3: the downstream stage of §2 with parameters `(μ, α, L)`
and shocks `ε`, feeding its orders `q` to an upstream stage with lead time `K` that forecasts
with `β = α / (1 + L α)`. -/
def IsTwoStage (μ α : ℝ) (L K : ℕ) (ε d F q x G p y : ℤ → ℝ) : Prop :=
  IsStage μ α L ε d F q x ∧ IsUpstream μ (upBeta α L) K q G p y

/-- The shock sequence with the paper's convention `ε_t = 0` for `t ≤ 0` (used in P1 and P2). -/
def masked (e : ℤ → ℝ) : ℤ → ℝ := fun s => if 1 ≤ s then e s else 0

end GravesIMA.Stages


