-- Prove2me | Definitions.Def_PeakEndPricing_Convergence_Model
-- name    : PeakEndPricing_Convergence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:30.555161+00:00
-- url     : https://prove2.me/theorems/fccfbe72-7b52-4b0c-88fd-53425e2d1aed
-- title:
--   The peak-end pricing model of §2–§3: kinked linear demand (4)–(6), Assumption 1, paths (2), value J (3), optimal paths, steady states, Problem (8), equations (9)–(12)
-- statement:
--   This file sets up the dynamic pricing model of Nasiry and Popescu (§2 and §3), in which consumers anchor on the **lowest price** seen so far and on the **last price** (the peak-end rule).
--
--   **Prices and demand.** A firm sets a price $p_t$ in the price set $\mathbf P = [0,\bar p]$ in every period $t = 1, 2, \dots$. Let $d_0$ be the **base demand** and $\pi_0(p) = p\,d_0(p)$ the **base profit**. With loss-aversion and gain sensitivities $\lambda \ge \gamma > 0$, demand at price $p$ and reference price $r$ is (4)
--   $$d(p,r) = d_0(p) - \lambda (p-r)^+ + \gamma (r-p)^+ ,$$
--   the short-term profit is $\pi(p,r) = p\,d(p,r)$ (5), and the smooth profits are (6)
--   $$\pi_k(p,r) = \pi_0(p) + k(r-p)p, \qquad k \in \{\lambda,\gamma\}.$$
--
--   **Assumption 1** (pp. 7–8): on $\mathbf P$, $d_0$ is non-negative, bounded, continuous and decreasing; $\pi_0$ is non-monotone and strictly concave; and $\bar p$ satisfies $d_0(\bar p) = 0$. The standing hypotheses of Section 3 add $\lambda \ge \gamma > 0$, $\theta \in (0,1]$, $\beta \in (0,1)$, and differentiability of $\pi_0$ on $\mathbf P$.
--
--   **Peak-end reference price** (2). Given an initial state $(m_0, p_0)$, the minimum price is $m_t = \min(m_{t-1}, p_t)$ and the reference price of period $t$ is
--   $$r_t = \theta m_{t-1} + (1-\theta) p_{t-1}.$$
--
--   **The firm's problem** (3), (7). The value function is
--   $$J(m_0,p_0) = \sup_{p_t \in \mathbf P} \sum_{t=1}^{\infty} \beta^{t-1} \pi(p_t, r_t),$$
--   the supremum over all price sequences in $\mathbf P$. An **optimal price path** from $(m_0,p_0)$ is a price sequence in $\mathbf P$ that attains $J(m_0,p_0)$. A **steady state** of Problem (7) is a state $(m,p)$ with $m, p \in \mathbf P$ and $m \le p$ from which the constant path $p_t \equiv p$ is optimal.
--
--   **The smooth Problem (8).** For $\nu \in [0,1]$ and $m \in \mathbf P$, $J^\nu_m(p_0)$ is the supremum over price sequences in $\mathbf P$ of
--   $$\sum_{t=1}^\infty \beta^{t-1}\Big[(1-\nu)\,\pi_\lambda\big(p_t, \theta m + (1-\theta)p_{t-1}\big) + \nu\, \pi_\gamma(p_t, p_{t-1})\Big],$$
--   and a steady state of Problem (8) is a price $p \in \mathbf P$ from which the constant path $p_t \equiv p$ attains $J^\nu_m(p)$.
--
--   **Equations (9)–(12).** With $\pi_0'$ the derivative of $\pi_0$:
--   $$\text{(9)}\quad \pi_0'(p) - \lambda(1-\beta(1-\theta))p = 0, \qquad \text{(10)}\quad \pi_0'(p) - \gamma(1-\beta)p = 0,$$
--   $$\text{(11)}\quad \pi_0'(p) - \big[\lambda(1-\nu)(2-(1-\theta)(1+\beta)) + \nu\gamma(1-\beta)\big]p + \lambda(1-\nu)\theta m = 0,$$
--   $$\text{(12)}\quad \pi_0'(p) - \lambda(2-(1-\theta)(1+\beta))p + \lambda\theta m = 0.$$
--   The roots $s$ of (9) and $S$ of (10) in $\mathbf P$ split the minimum prices into the regions $\mathbf R_1 = [0,s]$, $\mathbf R_2 = [s,S]$, $\mathbf R_3 = [S,\bar p]$; the root of (12) is the steady-state price $p^{**}_\lambda(m)$.
--
--   **Supermodularity** (p. 9): $f(x,y)$ is supermodular on $A \times B$ if $f(x_h,y_h) - f(x_l,y_h) \ge f(x_h,y_l) - f(x_l,y_l)$ for all $x_l < x_h$ in $A$ and $y_l < y_h$ in $B$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** A price path is a sequence $q : \mathbb N \to \mathbb R$ with $q(n) = p_{n+1}$; `price p0 q n` is $p_n$ (with $p_0$ at index $0$), `minPrice m0 q n` is $m_n$, and `refPrice θ m0 p0 q n` $= \theta m_n + (1-\theta)p_n$ is the reference price $r_{n+1}$ faced by $q(n)$. $J$ and $J^\nu_m$ are defined directly as suprema over the (nonempty) type of sequences $\mathbb N \to [0,\bar p]$, never as solutions of a Bellman equation; steady states are defined as optimal constant paths, never through (11)/(12). Lean's real `⨆` and `∑'` return $0$ on an unbounded family or a non-summable series; with $m_0, p_0 \in \mathbf P$, $0<\beta<1$ and $d_0$ continuous on $\mathbf P$, profits along every $\mathbf P$-valued path are bounded, every series is summable and the family is bounded, so these defaults are not reached on the domain the theorems use. The profit $\pi$ is defined by (4)–(5), not as $\min(\pi_\lambda,\pi_\gamma)$; that identity is Lemma 2. Assumption 1(a) is not a separate hypothesis: for the linear demand (4) with $\lambda,\gamma>0$ and $d_0$ decreasing it holds automatically. Assumption 1 never posits differentiability, but (9)–(12) use $\pi_0'$; the hypothesis `Standing.differentiable` asks $\pi_0$ to be differentiable (as a function on $\mathbb R$) at every point of $\mathbf P$, and $\pi_0'$ is Lean's `deriv`. "Increasing"/"decreasing" are weak throughout.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, pp. 6–11, §2, §3, (2)–(12), Assumption 1

import Mathlib

namespace PeakEndPricing.Convergence

/-- The base profit `π₀(p) = p d₀(p)` (p. 7). -/
noncomputable def baseProfit (d0 : ℝ → ℝ) (p : ℝ) : ℝ := p * d0 p

/-- Assumption 1 (b), (c) of the paper (pp. 7–8), together with the normalisation `d₀(p̄) = 0`
(p. 8), on the price set `P = [0, p̄]`. Part (a) is automatic for the linear demand (4). -/
structure Assumption1 (pbar : ℝ) (d0 : ℝ → ℝ) : Prop where
  /-- (b) `d₀` is non-negative on `P`. -/
  nonneg : ∀ p ∈ Set.Icc (0 : ℝ) pbar, 0 ≤ d0 p
  /-- (b) `d₀` is bounded on `P`. -/
  bounded : BddAbove (d0 '' Set.Icc (0 : ℝ) pbar)
  /-- (b) `d₀` is continuous on `P`. -/
  continuous : ContinuousOn d0 (Set.Icc (0 : ℝ) pbar)
  /-- (b) `d₀` is (weakly) decreasing on `P`. -/
  decreasing : AntitoneOn d0 (Set.Icc (0 : ℝ) pbar)
  /-- (c) `π₀` is non-monotone on `P`. -/
  nonmonotone : ¬ MonotoneOn (baseProfit d0) (Set.Icc (0 : ℝ) pbar) ∧
    ¬ AntitoneOn (baseProfit d0) (Set.Icc (0 : ℝ) pbar)
  /-- (c) `π₀` is strictly concave on `P`. -/
  strictConcave : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) pbar) (baseProfit d0)
  /-- p. 8: `p̄` is such that `d₀(p̄) = 0`. -/
  demand_pbar : d0 pbar = 0

/-- The standing hypotheses of Section 3: Assumption 1, differentiability of `π₀` on `P`
(used by (9)–(12) through `π₀'`, made explicit here), `λ ≥ γ > 0` (p. 9),
`θ ∈ (0, 1]` (p. 8) and `β ∈ (0, 1)` (p. 8). -/
structure Standing (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ) : Prop where
  assumption1 : Assumption1 pbar d0
  differentiable : ∀ p ∈ Set.Icc (0 : ℝ) pbar, DifferentiableAt ℝ (baseProfit d0) p
  gam_pos : 0 < gam
  gam_le_lam : gam ≤ lam
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  beta_pos : 0 < beta
  beta_lt_one : beta < 1

/-- Demand (4): `d(p, r) = d₀(p) − λ (p − r)⁺ + γ (r − p)⁺`. -/
noncomputable def demand (d0 : ℝ → ℝ) (lam gam p r : ℝ) : ℝ :=
  d0 p - lam * max (p - r) 0 + gam * max (r - p) 0

/-- Short-term profit (5): `π(p, r) = p · d(p, r)`. -/
noncomputable def profit (d0 : ℝ → ℝ) (lam gam p r : ℝ) : ℝ :=
  p * demand d0 lam gam p r

/-- The smooth profit functions (6): `π_k(p, r) = π₀(p) + k (r − p) p`, for `k ∈ {λ, γ}`. -/
noncomputable def profitK (d0 : ℝ → ℝ) (k p r : ℝ) : ℝ :=
  baseProfit d0 p + k * (r - p) * p

/-- The price sequence `p_t`, indexed by `t`: `price p0 q 0 = p₀` and `price p0 q (n+1) = q n`,
where the decision sequence `q` lists `p₁, p₂, …` (`q n = p_{n+1}`). -/
def price (p0 : ℝ) (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => p0
  | n + 1 => q n

/-- The running minimum price `m_t = min(m₀, p₁, …, p_t)`, indexed by `t`:
`minPrice m0 q 0 = m₀`, `minPrice m0 q (n+1) = min (m_n) (p_{n+1})`. -/
def minPrice (m0 : ℝ) (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => m0
  | n + 1 => min (minPrice m0 q n) (q n)

/-- The peak-end reference price (2): `refPrice theta m0 p0 q n = θ m_n + (1 − θ) p_n`, which is
the reference price `r_{n+1}` faced by the decision `q n = p_{n+1}`. -/
noncomputable def refPrice (theta m0 p0 : ℝ) (q : ℕ → ℝ) (n : ℕ) : ℝ :=
  theta * minPrice m0 q n + (1 - theta) * price p0 q n

/-- Discounted profit of a price sequence: `∑_{t ≥ 1} β^{t−1} π(p_t, r_t)`. -/
noncomputable def pathValue (d0 : ℝ → ℝ) (lam gam theta beta m0 p0 : ℝ) (q : ℕ → ℝ) : ℝ :=
  ∑' n, beta ^ n * profit d0 lam gam (q n) (refPrice theta m0 p0 q n)

/-- The value function `J(m₀, p₀)` of Problem (3)/(7) (p. 8): the supremum of the discounted
profit over all price sequences in `P = [0, p̄]`. -/
noncomputable def J (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta m0 p0 : ℝ) : ℝ :=
  ⨆ q : ℕ → Set.Icc (0 : ℝ) pbar, pathValue d0 lam gam theta beta m0 p0 (fun n => (q n : ℝ))

/-- An optimal price path from the state `(m₀, p₀)`: a sequence `q` of prices in `P`
(`q n = p_{n+1}`) whose discounted profit attains `J(m₀, p₀)`. -/
def IsOptimalPath (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta m0 p0 : ℝ) (q : ℕ → ℝ) : Prop :=
  (∀ n, q n ∈ Set.Icc (0 : ℝ) pbar) ∧
    pathValue d0 lam gam theta beta m0 p0 q = J pbar d0 lam gam theta beta m0 p0

/-- A steady state of Problem (7): a state `(m, p)` with `m, p ∈ P`, `m ≤ p`, from which the
constant price path `p_t ≡ p` is optimal. -/
def IsSteadyState (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta m p : ℝ) : Prop :=
  m ∈ Set.Icc (0 : ℝ) pbar ∧ p ∈ Set.Icc (0 : ℝ) pbar ∧ m ≤ p ∧
    IsOptimalPath pbar d0 lam gam theta beta m p (fun _ => p)

/-- Discounted profit of a price sequence in the smooth Problem (8) with parameters `ν`, `m`:
`∑_{t ≥ 1} β^{t−1} [(1 − ν) π_λ(p_t, θ m + (1 − θ) p_{t−1}) + ν π_γ(p_t, p_{t−1})]`. -/
noncomputable def auxPathValue (d0 : ℝ → ℝ) (lam gam theta beta m nu p0 : ℝ) (q : ℕ → ℝ) : ℝ :=
  ∑' n, beta ^ n * ((1 - nu) * profitK d0 lam (q n) (theta * m + (1 - theta) * price p0 q n) +
    nu * profitK d0 gam (q n) (price p0 q n))

/-- The value function `J^ν_m(p₀)` of Problem (8) (p. 10): the supremum of `auxPathValue` over
all price sequences in `P`. -/
noncomputable def auxValue (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta m nu p0 : ℝ) : ℝ :=
  ⨆ q : ℕ → Set.Icc (0 : ℝ) pbar,
    auxPathValue d0 lam gam theta beta m nu p0 (fun n => (q n : ℝ))

/-- A steady state of Problem (8): a price `p ∈ P` from which the constant path `p_t ≡ p` attains
`J^ν_m(p)`. -/
def IsAuxSteadyState (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta m nu p : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) pbar ∧
    auxPathValue d0 lam gam theta beta m nu p (fun _ => p) = auxValue pbar d0 lam gam theta beta m nu p

/-- Equation (9): `π₀'(p) − λ(1 − β(1 − θ)) p = 0` (its root in `P` is the threshold `s`). -/
def eq9 (d0 : ℝ → ℝ) (lam theta beta p : ℝ) : Prop :=
  deriv (baseProfit d0) p - lam * (1 - beta * (1 - theta)) * p = 0

/-- Equation (10): `π₀'(p) − γ(1 − β) p = 0` (its root in `P` is the threshold `S`). -/
def eq10 (d0 : ℝ → ℝ) (gam beta p : ℝ) : Prop :=
  deriv (baseProfit d0) p - gam * (1 - beta) * p = 0

/-- Equation (11):
`π₀'(p) − [λ(1 − ν)(2 − (1 − θ)(1 + β)) + νγ(1 − β)] p + λ(1 − ν)θ m = 0`. -/
def eq11 (d0 : ℝ → ℝ) (lam gam theta beta m nu p : ℝ) : Prop :=
  deriv (baseProfit d0) p -
      (lam * (1 - nu) * (2 - (1 - theta) * (1 + beta)) + nu * gam * (1 - beta)) * p +
      lam * (1 - nu) * theta * m = 0

/-- Equation (12): `π₀'(p) − λ(2 − (1 − θ)(1 + β)) p + λθ m = 0` (its root is `p**_λ(m)`). -/
def eq12 (d0 : ℝ → ℝ) (lam theta beta m p : ℝ) : Prop :=
  deriv (baseProfit d0) p - lam * (2 - (1 - theta) * (1 + beta)) * p + lam * theta * m = 0

/-- Supermodularity (p. 9): `f(x_h, y_h) − f(x_l, y_h) ≥ f(x_h, y_l) − f(x_l, y_l)` for all
`x_l < x_h` in `A` and `y_l < y_h` in `B`. -/
def SupermodularOn (f : ℝ → ℝ → ℝ) (A B : Set ℝ) : Prop :=
  ∀ xl ∈ A, ∀ xh ∈ A, ∀ yl ∈ B, ∀ yh ∈ B, xl < xh → yl < yh →
    f xh yh - f xl yh ≥ f xh yl - f xl yl

end PeakEndPricing.Convergence


