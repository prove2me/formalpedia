-- Prove2me | Definitions.Def_PochetWolsey_BacklogStartup_JointModel
-- name    : PochetWolsey_BacklogStartup_JointModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:30:34.799113+00:00
-- url     : https://prove2.me/theorems/824d2653-26ee-428b-a397-475ee06b2d7a
-- title:
--   Joint backlogging and start-up model and extended LP
-- statement:
--   For $n$ periods, let $d$ be demand, $x$ production, $s$ stock, $r$ backlog, $y$ setups, $z$ start-ups, and $w$ switch-offs. Stocks and backlogs have indices $0,\ldots,n$; switch-offs have indices $0,\ldots,n-1$; other vectors have indices $1,\ldots,n$. For a given initial setup state $y_0\in\{0,1\}$, the original mixed-integer set $X(y_0,d,M)$ has $x,s,r\ge0$, $r_0=0$, binary $y,z,w$, and
--   $$s_{t-1}-r_{t-1}+x_t=d_t+s_t-r_t,\quad x_t\le My_t,\quad z_t-w_{t-1}=y_t-y_{t-1},\quad z_t\le y_t.$$
--
--   The extended set $Q(y_0,d)$ retains the nonnegative domains, $r_0=0$, and switch equations, replaces the binary domains by unit boxes, and introduces nonnegative fractions $\alpha,\beta$. Its additional constraints are
--   $$\alpha_t+y_t+\beta_t=1\quad(d_t>0),\qquad \beta_t\le\beta_{t+1}+z_{t+1}\quad(1\le t<n),$$
--   $$s_{t-1}\ge\sum_{u=t}^k d_u\left(\alpha_u-\sum_{j=t}^{u-1}w_j\right)\quad(1\le t\le k\le n),$$
--   $$r_t\ge\sum_{u=k}^t d_u\left(\beta_u-\sum_{j=u+1}^{t}z_j\right)\quad(1\le k\le t\le n).$$
--   The projection of $Q(y_0,d)$ existentially eliminates $\alpha,\beta$. It is not defined as a convex hull. The cost of a plan is
--   $$C(s,r,y,z)=\sum_{t=0}^n h_ts_t+\sum_{t=1}^n(b_tr_t+q_ty_t+g_tz_t).$$
--   Wagner–Whitin costs mean $h_t\ge0$ and $b_t\ge0$ at every listed index.
--
--   These definitions distinguish the physical mixed-integer formulation from its extended optimization formulation.
--
--   **Formalization Note** The LP has no production balance or production/setup bound: its displayed $x\ge0$ is cost-free and otherwise unused. The theorem concerns attained optimal costs, not identity of feasible sets or production recovery for every LP point. Nonnegativity of $\alpha,\beta$ is inherited from their fraction domains in Section 10.2.3; Section 10.6 omits their domain line. Adjacent-period constraints stop at $n-1$. The $n$ switch-offs are $w_0,\ldots,w_{n-1}$, the indices used by the $n$ switch equations; there is no $w_n$ decision or equation at $n+1$. In particular $w_0$ is not fixed to zero. Initial stock and terminal stock/backlog remain free and nonnegative. Setup and start-up costs are real without added sign restrictions.
--
--   Initial-state convention: the parameter `y0` is the same fixed binary datum in every feasible set in this item (printed p. 138 / PDF 155); it is not optimized.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, pp. 308, 330–331 (PDF 321, 343–344), Sections 10.2.3 and 10.6; initial setup datum: p. 138 (PDF 155), Section 4.3.6

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_Horizon

namespace PochetWolsey.BacklogStartup

noncomputable section

structure JointPoint (n : ℕ) where
  x : Fin n → ℝ
  s : Fin (n + 1) → ℝ
  r : Fin (n + 1) → ℝ
  y : Fin n → ℝ
  z : Fin n → ℝ
  w : Fin n → ℝ

structure JointLift (n : ℕ) where
  point : JointPoint n
  alpha : Fin n → ℝ
  beta : Fin n → ℝ

structure JointCosts (n : ℕ) where
  h : Fin (n + 1) → ℝ
  b : Fin n → ℝ
  q : Fin n → ℝ
  g : Fin n → ℝ

/-- Both kinds of carrying cost are nonnegative after eliminating production costs. -/
def JointCosts.WagnerWhitin {n : ℕ} (c : JointCosts n) : Prop :=
  (∀ t, 0 ≤ c.h t) ∧ (∀ t, 0 ≤ c.b t)

def jointCost {n : ℕ} (c : JointCosts n) (p : JointPoint n) : ℝ :=
  (∑ t, c.h t * p.s t) +
  ∑ t : Fin n, (c.b t * stock p.r (t.val + 1) + c.q t * p.y t + c.g t * p.z t)

/-- The common domains and switch balance, with given y₀, switch-offs w₀,...,w_(n-1), and r₀ = 0. -/
def JointCore {n : ℕ} (y0 : ℝ) (p : JointPoint n) : Prop :=
  (∀ t, 0 ≤ p.x t) ∧ (∀ t, 0 ≤ p.s t) ∧ (∀ t, 0 ≤ p.r t) ∧
  stock p.r 0 = 0 ∧
  (∀ t ∈ Finset.Icc 1 n,
    period p.z t - switchOff p.w (t - 1) = period p.y t - setupState y0 p.y (t - 1) ∧
    period p.z t ≤ period p.y t)

/-- Original mixed-integer formulation on printed p. 330. -/
def JointFeasible {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) (M : ℝ) : Set (JointPoint n) :=
  {p | JointCore y0 p ∧ Binary p.y ∧ Binary p.z ∧ Binary p.w ∧
    ∀ t ∈ Finset.Icc 1 n,
      stock p.s (t - 1) - stock p.r (t - 1) + period p.x t =
        period d t + stock p.s t - stock p.r t ∧
      period p.x t ≤ M * period p.y t}

/-- The displayed extended LP on pp. 330-331. Alpha and beta retain their
nonnegative fraction domains from Section 10.2.3. The adjacent-period inequality
has range 1 ≤ t < n; switch-offs have indices 0,...,n-1. -/
def JointExtended {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) : Set (JointLift n) :=
  {v | JointCore y0 v.point ∧ UnitBox v.point.y ∧ UnitBox v.point.z ∧
    UnitBox v.point.w ∧ (∀ t, 0 ≤ v.alpha t) ∧ (∀ t, 0 ≤ v.beta t) ∧
    (∀ t ∈ Finset.Icc 1 n, 0 < period d t →
      period v.alpha t + period v.point.y t + period v.beta t = 1) ∧
    (∀ t ∈ Finset.Icc 1 (n - 1),
      period v.beta t ≤ period v.beta (t + 1) + period v.point.z (t + 1)) ∧
    (∀ t ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc t n,
      (∑ u ∈ Finset.Icc t k, period d u *
        (period v.alpha u - ∑ j ∈ Finset.Icc t (u - 1), switchOff v.point.w j)) ≤
          stock v.point.s (t - 1)) ∧
    (∀ k ∈ Finset.Icc 1 n, ∀ t ∈ Finset.Icc k n,
      (∑ u ∈ Finset.Icc k t, period d u *
        (period v.beta u - ∑ j ∈ Finset.Icc (u + 1) t, period v.point.z j)) ≤
          stock v.point.r t)}

/-- Projection of the lift is existential elimination, not a hull definition. -/
def JointProjection {n : ℕ} (y0 : ℝ) (d : Fin n → ℝ) : Set (JointPoint n) :=
  {p | ∃ a b : Fin n → ℝ, JointLift.mk p a b ∈ JointExtended y0 d}

end
end PochetWolsey.BacklogStartup


