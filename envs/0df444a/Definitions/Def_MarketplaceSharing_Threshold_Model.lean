-- Prove2me | Definitions.Def_MarketplaceSharing_Threshold_Model
-- name    : MarketplaceSharing_Threshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:42.232128+00:00
-- url     : https://prove2.me/theorems/c64ce810-3cd7-4a96-a853-5515312dbac5
-- title:
--   §3.1–3.2, pp. 6–10 — inventory-sharing parameters, the HJB system (3) with V₀ ≡ 0 and Vₙ(0) = 0, ΔVₙ, the HJB maximizer, the threshold tₙ ∈ [0, ∞], the class (4)
-- statement:
--   This file fixes the continuous-time **inventory sharing** model of Martínez-de-Albéniz, Pinto and Amorim. A supplier holds a finite stock of an item and sells it during a season at the price $\pi$ through its own channel, where customers arrive as a Poisson process of rate $\lambda_D$. At every moment it may also *share* its inventory with a marketplace platform, whose customers arrive at rate $\lambda_P$; on a platform sale the supplier keeps $(1-\theta)\pi$ and the platform takes the commission $\theta\pi$. Revenue is discounted at rate $r$. Time $t \ge 0$ is the **time-to-go** until the end of the season.
--
--   **Parameters.** A parameter set is $(\pi, \theta, \lambda_D, \lambda_P, r)$ with $\theta \in [0,1]$, $\pi > 0$, $\lambda_D > 0$, $\lambda_P > 0$ and $r \ge 0$. The **platform margin** is $(1-\theta)\pi$.
--
--   **The HJB equation.** For a decision $z \in \{0,1\}$ ($z = 1$: share), a marginal value $\Delta$ and a value $v$, the bracket of the HJB equation (3) is
--   $$H_z(\Delta, v) = \bigl(\pi\lambda_D + z(1-\theta)\pi\lambda_P\bigr) - (\lambda_D + z\lambda_P)\,\Delta - r v,$$
--   and its right-hand side is $\max_{z\in\{0,1\}} H_z(\Delta, v)$. A family $(V_n)_{n \ge 0}$ of functions of the time-to-go is a **revenue-to-go** if $V_0(t) = 0$ for $t \ge 0$, $V_n(0) = 0$ for all $n$, and for every $n \ge 1$ and $t \ge 0$
--   $$\frac{dV_n}{dt}(t) = \max_{z\in\{0,1\}} H_z\bigl(\Delta V_n(t), V_n(t)\bigr), \qquad \Delta V_n(t) = V_n(t) - V_{n-1}(t),$$
--   with a one-sided derivative at $t = 0$. $\Delta V_n$ is the **marginal revenue-to-go** of the $n$-th unit.
--
--   **Optimal decisions and the threshold.** A decision $z$ is **optimal** for unit $n$ at time-to-go $t$ if it attains the maximum above at $(\Delta V_n(t), V_n(t))$. The **threshold** of unit $n \ge 1$ is
--   $$t_n = \sup\{t \ge 0 : \Delta V_n(t) \le (1-\theta)\pi\} \in [0, \infty],$$
--   with $t_0 = 0$; it equals $\infty$ when $\Delta V_n$ never exceeds $(1-\theta)\pi$, the paper's convention "when there is no finite solution then we can set $t_n = \infty$".
--
--   **The closed-form class (4).** A function $f$ has the form (4) for indices $1 \le j \le n+1$ on a set $S$ if there are constants $C$, $A_0,\dots,A_{n-j}$ and $B_0,\dots,B_{j-2}$ such that for all $t \in S$
--   $$f(t) = C + \sum_{i=0}^{n-j} A_i\, t^i e^{-(\lambda_D+\lambda_P+r)t} + \sum_{i=0}^{j-2} B_i\, t^i e^{-(\lambda_D+r)t}.$$
--
--   These objects are shared by every statement of the mission: the threshold structure of Theorem 1, Lemmas 1–4 and Corollary 1 are all statements about a revenue-to-go in this sense.
--
--   **Formalization Note.** The paper defines $V_n$ by the stochastic control problem (2) and derives (3) from it informally; here $V_n$ is any solution of (3), and the theorems take it as a hypothesis (a separate milestone shows a solution exists and is unique on $[0,\infty)$). Decisions are Booleans (`true` = share). $\pi > 0$, $\lambda_D > 0$, $\lambda_P > 0$ and $r \ge 0$ are added standing hypotheses; $\theta \in [0,1]$ is printed on p. 6. The threshold is an extended real; its defining set always contains $0$ for a revenue-to-go, so it is never empty. In (4) the exponents carry $r$, as the proof on p. 30 does; the printed display omits $r$, which is exact only at $r = 0$. Values of $V_n$ at $t < 0$ are unconstrained.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), pp. 6–10, §3.1–3.2, eqs. (1)–(4); Appendix p. 28 (Vₙ(0) = 0); p. 10 (tₙ = ∞ convention)

import Mathlib

namespace MarketplaceSharing.Threshold

/-- The parameters of the Inventory Sharing problem (§3.1, pp. 6–8, of Martínez-de-Albéniz, Pinto &
Amorim, *Driving Supply to Marketplaces*, SSRN 3643261): selling price `π` (`price`), platform
commission `θ ∈ [0, 1]`, Poisson arrival rates `λD` (direct channel, `lamD`) and `λP` (platform,
`lamP`), and discount rate `r ≥ 0`. `θ ∈ [0, 1]` is printed on p. 6; `0 < π`, `0 < λD`, `0 < λP`
and `0 ≤ r` are added, disclosed standing hypotheses. -/
structure Params where
  price : ℝ
  θ : ℝ
  lamD : ℝ
  lamP : ℝ
  r : ℝ
  price_pos : 0 < price
  θ_nonneg : 0 ≤ θ
  θ_le_one : θ ≤ 1
  lamD_pos : 0 < lamD
  lamP_pos : 0 < lamP
  r_nonneg : 0 ≤ r

/-- The marginal revenue-to-go `ΔVₙ(t) = Vₙ(t) − Vₙ₋₁(t)` (p. 8), for `V : ℕ → ℝ → ℝ` indexed by
units left and time-to-go. Only used for `n ≥ 1`. -/
def marginal (V : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := V n t - V (n - 1) t

namespace Params

variable (p : Params)

/-- The supplier's margin on a platform sale, `(1 − θ)π` (p. 6, p. 8). -/
def platformMargin : ℝ := (1 - p.θ) * p.price

/-- The bracket of the HJB equation (3), p. 8, for the decision `z ∈ {0, 1}` (`false`/`true`):
`(πλD + z(1 − θ)πλP) − (λD + zλP)Δ − rv`, with `Δ = ΔVₙ(t)` and `v = Vₙ(t)`. -/
def hamiltonian (z : Bool) (Δ v : ℝ) : ℝ :=
  p.price * p.lamD + (if z then 1 else 0) * ((1 - p.θ) * p.price * p.lamP)
    - (p.lamD + (if z then 1 else 0) * p.lamP) * Δ - p.r * v

/-- The right-hand side `sup_{z ∈ {0,1}} [⋯]` of (3). -/
def hjbRHS (Δ v : ℝ) : ℝ := max (p.hamiltonian false Δ v) (p.hamiltonian true Δ v)

/-- `V : ℕ → ℝ → ℝ` (units left, time-to-go) solves the HJB system (3) (p. 8) with `V₀ ≡ 0` (no
units, no revenue) and `Vₙ(0) = 0` (p. 28: "for all n, Vn(0) = 0"): for every `n ≥ 1` and `t ≥ 0`,
`Vₙ` has derivative `sup_z [⋯]` at `t` within `[0, ∞)` (one-sided at `t = 0`). Values at `t < 0`
are unconstrained. -/
structure IsRevenueToGo (V : ℕ → ℝ → ℝ) : Prop where
  zero_units : ∀ t : ℝ, 0 ≤ t → V 0 t = 0
  zero_time : ∀ n, V n 0 = 0
  hjb : ∀ n, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (V n) (p.hjbRHS (V n t - V (n - 1) t) (V n t)) (Set.Ici 0) t

/-- The decision `z` (`true` = share the `n`-th unit, `false` = do not) attains the supremum of the
bracket of (3) at `(t, n)`, i.e. it is an optimal sharing decision there. -/
def IsOptimalDecision (V : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) (z : Bool) : Prop :=
  ∀ z' : Bool, p.hamiltonian z' (marginal V n t) (V n t) ≤ p.hamiltonian z (marginal V n t) (V n t)

/-- The threshold `tₙ ∈ [0, ∞]` (Theorem 1, p. 9): `sup {t ≥ 0 | ΔVₙ(t) ≤ (1 − θ)π}` in `EReal`.
The set always contains `0` when `Vₙ(0) = Vₙ₋₁(0) = 0`, and its supremum is `⊤` exactly when it is
unbounded, which is p. 10's convention `tₙ = ∞` when `ΔVₙ(t) = (1 − θ)π` has no finite solution.
`t₀ := 0`, the left end of the interval `I_{n1}`. -/
noncomputable def threshold (V : ℕ → ℝ → ℝ) (n : ℕ) : EReal :=
  if n = 0 then 0
  else sSup ((fun t : ℝ => (t : EReal)) '' {t : ℝ | 0 ≤ t ∧ marginal V n t ≤ p.platformMargin})

end Params

/-- The closed form (4), p. 9, on a set `S`: there are constants `C`, `A₀, …, A_{n−j}` and
`B₀, …, B_{j−2}` with, for every `t ∈ S`,
`f t = C + Σ_{i=0}^{n−j} Aᵢ tⁱ e^{−(λD+λP+r)t} + Σ_{i=0}^{j−2} Bᵢ tⁱ e^{−(λD+r)t}`.
The exponents carry the discount rate `r`, as in the proof on p. 30; the printed (4) omits it,
which is exact only at `r = 0`. Meant for `1 ≤ j ≤ n + 1` (the `A`-sum is empty at `j = n + 1`,
the `B`-sum at `j = 1`). -/
def ClosedFormOn (p : Params) (f : ℝ → ℝ) (n j : ℕ) (S : Set ℝ) : Prop :=
  ∃ (C : ℝ) (A B : ℕ → ℝ), ∀ t ∈ S,
    f t = C + ∑ i ∈ Finset.range (n + 1 - j), A i * t ^ i * Real.exp (-(p.lamD + p.lamP + p.r) * t)
      + ∑ i ∈ Finset.range (j - 1), B i * t ^ i * Real.exp (-(p.lamD + p.r) * t)

end MarketplaceSharing.Threshold


