-- Prove2me | Definitions.Def_HybridOrderAlloc_Thickness_Model
-- name    : HybridOrderAlloc_Thickness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:28.628345+00:00
-- url     : https://prove2.me/theorems/e78ed928-6fe2-4f0f-a871-bb816a18d99a
-- title:
--   §3, (1)–(5), (14), (17), Assumptions 1–2, Definition 1, pp. 7–15, 35–37 — the order-allocation DP, its value functions, the regions R1–R3, y^U, L, G
-- statement:
--   The model of He & Goh's *Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce*: a firm that can transfer part of its demand to its own freelancer platform, over $T$ periods.
--
--   **Data.** A probability space $(\Omega, P)$ carries the one-period shocks: the cross-network effect $\beta$, the spillover $\theta$ of market thickness on firm demand, and the firm-demand noise $\epsilon$. The parameters are the per-order price $p$, the firm's marginal revenue $r$, the relative inefficiency $R$ of freelancers, the natural growth coefficient $\rho$, the wage effectiveness $\delta$, the demand persistence $\eta$, the discount factor $\gamma$ and the horizon $T\in\mathbb N$.
--
--   **Standing assumptions** (§3): $p>0$, $r<p$, $R\ge1$, $\rho,\delta,\eta\ge0$, $\gamma\in[0,1]$; $\beta\ge0$ almost surely with $\mathbb E\beta^2<\infty$ (Assumption 2); $\theta,\epsilon$ square integrable and independent with $\mu_\theta:=\mathbb E\theta\ge0$ (3). Added and disclosed: $r\ge0$, $T\ge1$, and almost surely $\rho+\delta R\beta>0$, $\theta\ge0$, $\epsilon\ge0$.
--
--   **Value functions** (5). The state is the market thickness $M>0$ and the firm demand $D\ge0$; the decision is the transfer quantity $0\le y\le D$. With $V_{T+1}:=0$ and, for $t=1,\dots,T$,
--   $$V_t(M,D)=\max_{0\le y\le D}\ r(D-y)+\mathbb E\Big[p(y+\beta M)\Big(1-\frac{R(y+\beta M)}{M}\Big)\Big]+\gamma\,\mathbb E\big[V_{t+1}\big((\rho+\delta R\beta)M+\delta Ry,\ \eta D+\theta M+\epsilon\big)\big].$$
--   The payout ratio $\alpha=R(y+\beta M)/M$ (from (1) with the linear supply curve of Assumption 1) and the market-thickness update (4) are substituted as on the page.
--
--   **Parameters.** $\mu:=\mathbb E\beta$, $\sigma^2:=\operatorname{Var}\beta$, $\tilde\mu:=\mu-R\sigma^2-R\mu^2$, $\mu_0:=(p-r)/(2pR)$ and $\Delta:=\frac{\gamma r\mu_\theta}{p}\sum_{j\ge0}\gamma^j\eta^j$, which is $+\infty$ when $\gamma\eta\ge1$.
--
--   **Regions** (6), all inside $\{\mu>0,\ \sigma^2>0\}$:
--   $$\mathcal R_1:\ \sigma^2>\frac{\mu}{R}-\mu^2+(\mu_0-\mu)_+^2+\frac{\Delta}{R},\qquad \mathcal R_2:\ \sigma^2<\frac{\mu}{R}-\mu^2,\qquad \mathcal R_3:\ \frac{\mu}{R}-\mu^2<\sigma^2<\frac{\mu}{R}-\mu^2+(\mu_0-\mu)_+^2+\frac{\Delta}{R}.$$
--   Market thickness **benefits** the system in period $t$ if $V_t(M,D)$ is (weakly) increasing in $M$ for every fixed $D>0$, and is **costly** if it is (weakly) decreasing; it is **costly in the limit as $M\to\infty$** if, for every $D>0$, $V_t(\cdot,D)$ is decreasing on some tail $[M_0,\infty)$.
--
--   **Auxiliary objects** (Appendix A). $\partial_1V_t$, $\partial_2V_t$ are the right partial derivatives; $y^U_t(M,D)$ is the infimum in (14) of the $y\ge0$ with $y\ge(\mu_0-\mu)M+\frac{\gamma\delta M}{2p}\mathbb E\,\partial_1V_{t+1}((\rho+\delta R\beta)M+\delta Ry,\ \eta D+\theta M+\epsilon)$; $L(t):=r\sum_{j=0}^{T-t}\gamma^j\eta^j$; and for integers $t\le T+1$,
--   $$G(t):=\sum_{i=0}^{T-t}\gamma^i(\rho+\delta R\mu)^i\Big(p\tilde\mu+\gamma r\mu_\theta\sum_{j=0}^{T-t-1-i}\gamma^j\eta^j\Big).\qquad(17)$$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** One shock vector $(\beta,\theta,\epsilon)$ serves every period: the per-period shocks are i.i.d. and (5) only uses their one-period law; the joint law of $\beta$ and $(\theta,\epsilon)$ is left free, as on the page. $V_t$ is defined by recursion on the number of periods to go, $V_t=\mathrm{Vto}(T+1-t)$, with the page's $\max$ written as a supremum over $[0,D]$ (attained by Lemma 1(c)). It is defined for $M>0$, $D\ge0$ because the next firm demand can be $0$. The expectation of the platform profit is kept as an integral, as printed in (5). The regions carry the guard $\gamma\eta<1$ wherever $\Delta$ is used, so that a divergent series never contributes the value $0$. $G$ is indexed by integers.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), pp. 7–15, 35–37, §3, (1)–(5), Assumptions 1–2, Definition 1 and (6); Appendix A Notation, (14), Lemma 2(b), (17)

import Mathlib

namespace HybridOrderAlloc.Thickness

open MeasureTheory ProbabilityTheory

/-- The primitive data of He & Goh's firm–platform order-allocation model (§3, pp. 7–14):
a probability space `P` on `Ω` carrying the one-period shocks `beta` (β, cross-network effect),
`theta` (θ, spillover of market thickness on firm demand) and `eps` (ϵ, firm-demand noise);
the per-order price `p`, the firm's marginal revenue `r`, the freelancer inefficiency `R`,
the natural growth coefficient `rho` (ρ), the wage effectiveness `delta` (δ), the demand
persistence `eta` (η), the discount factor `gam` (γ) and the horizon `T`.
The per-period shocks are i.i.d., so the Bellman recursion (5) only uses one shock vector. -/
structure Sys (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  beta : Ω → ℝ
  theta : Ω → ℝ
  eps : Ω → ℝ
  p : ℝ
  r : ℝ
  R : ℝ
  rho : ℝ
  delta : ℝ
  eta : ℝ
  gam : ℝ
  T : ℕ

namespace Sys

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The standing assumptions of §3 (pp. 7–14): `p > 0`, `r < p`, `R ≥ 1` ((1)), `ρ, δ ≥ 0` ((2)),
`η ≥ 0` ((3)), `γ ∈ [0,1]`, `T ≥ 1` periods; Assumption 2 (`β ≥ 0` a.s., `E β² < ∞`);
(3) (`θ`, `ϵ` independent and square integrable, `μ_θ = E θ ≥ 0`).
Added (disclosed): `r ≥ 0` (Theorem 1 is false for `r < 0`), and `ρ + δRβ > 0`, `θ ≥ 0`, `ϵ ≥ 0`
almost surely, which keep the next state of (5) in the domain `M > 0`, `D ≥ 0`. -/
structure Standing (S : Sys Ω) : Prop where
  p_pos : 0 < S.p
  r_lt_p : S.r < S.p
  r_nonneg : 0 ≤ S.r
  one_le_R : 1 ≤ S.R
  rho_nonneg : 0 ≤ S.rho
  delta_nonneg : 0 ≤ S.delta
  eta_nonneg : 0 ≤ S.eta
  gam_nonneg : 0 ≤ S.gam
  gam_le_one : S.gam ≤ 1
  one_le_T : 1 ≤ S.T
  isProb : IsProbabilityMeasure S.P
  beta_nonneg : ∀ᵐ ω ∂S.P, 0 ≤ S.beta ω
  beta_memLp : MemLp S.beta 2 S.P
  theta_memLp : MemLp S.theta 2 S.P
  eps_memLp : MemLp S.eps 2 S.P
  indep_theta_eps : IndepFun S.theta S.eps S.P
  muTheta_nonneg : 0 ≤ ∫ ω, S.theta ω ∂S.P
  growth_pos : ∀ᵐ ω ∂S.P, 0 < S.rho + S.delta * S.R * S.beta ω
  theta_nonneg : ∀ᵐ ω ∂S.P, 0 ≤ S.theta ω
  eps_nonneg : ∀ᵐ ω ∂S.P, 0 ≤ S.eps ω

/-- The objective of the Bellman equation (5), p. 14, for a continuation value `W`:
`r(D − y) + E[p(y + βM)(1 − R(y + βM)/M)] + γ E[W((ρ + δRβ)M + δRy, ηD + θM + ϵ)]`. -/
noncomputable def stage (S : Sys Ω) (W : ℝ → ℝ → ℝ) (M D y : ℝ) : ℝ :=
  S.r * (D - y) + ∫ ω, S.p * (y + S.beta ω * M) * (1 - S.R * (y + S.beta ω * M) / M) ∂S.P
    + S.gam * ∫ ω, W ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y)
        (S.eta * D + S.theta ω * M + S.eps ω) ∂S.P

/-- The value function with `k` periods to go: `Vto 0 = 0`, and `Vto (k+1) M D` is the
maximum over `0 ≤ y ≤ D` of the objective of (5) with continuation `Vto k`. -/
noncomputable def Vto (S : Sys Ω) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun M D => sSup (stage S (Vto S k) M D '' Set.Icc 0 D)

/-- The value function `V_t` of (5), p. 14: period `t` has `T + 1 − t` periods to go,
so `V (T + 1) = 0`. -/
noncomputable def V (S : Sys Ω) (t : ℕ) : ℝ → ℝ → ℝ := S.Vto (S.T + 1 - t)

/-- `µ := E(β)` (p. 11). -/
noncomputable def mu (S : Sys Ω) : ℝ := ∫ ω, S.beta ω ∂S.P

/-- `σ² := Var(β)` (p. 11). -/
noncomputable def sigma2 (S : Sys Ω) : ℝ := variance S.beta S.P

/-- `µ_θ := E(θ)` (p. 12). -/
noncomputable def muTheta (S : Sys Ω) : ℝ := ∫ ω, S.theta ω ∂S.P

/-- `µ̃ := µ − Rσ² − Rµ²` (Appendix A, Notation, p. 35). -/
noncomputable def muTilde (S : Sys Ω) : ℝ := S.mu - S.R * S.sigma2 - S.R * S.mu ^ 2

/-- `µ₀ := (p − r)/(2pR)` (Definition 1, p. 15). -/
noncomputable def mu0 (S : Sys Ω) : ℝ := (S.p - S.r) / (2 * S.p * S.R)

/-- `∆ := (γrµ_θ/p) Σ_{j≥0} γ^j η^j` (Definition 1, p. 15). Only meaningful when `γη < 1`;
every use is guarded by `γη < 1` (the page sets `∆ = +∞` when `γη ≥ 1`). -/
noncomputable def DeltaFin (S : Sys Ω) : ℝ :=
  S.gam * S.r * S.muTheta / S.p * ∑' j : ℕ, (S.gam * S.eta) ^ j

/-- `(µ, σ) ∈ R₁` (6): `σ² > µ/R − µ² + (µ₀ − µ)₊² + ∆/R`, with `∆ < ∞` (`γη < 1`). -/
def InR1 (S : Sys Ω) : Prop :=
  0 < S.mu ∧ 0 < S.sigma2 ∧ S.gam * S.eta < 1 ∧
    S.mu / S.R - S.mu ^ 2 + (max (S.mu0 - S.mu) 0) ^ 2 + S.DeltaFin / S.R < S.sigma2

/-- `(µ, σ) ∈ R₂` (6): `σ² < µ/R − µ²`. -/
def InR2 (S : Sys Ω) : Prop :=
  0 < S.mu ∧ 0 < S.sigma2 ∧ S.sigma2 < S.mu / S.R - S.mu ^ 2

/-- `(µ, σ) ∈ R₃` (6): `µ/R − µ² < σ² < µ/R − µ² + (µ₀ − µ)₊² + ∆/R`; the upper bound is
vacuous when `∆ = +∞` (`γη ≥ 1`). -/
def InR3 (S : Sys Ω) : Prop :=
  0 < S.mu ∧ 0 < S.sigma2 ∧ S.mu / S.R - S.mu ^ 2 < S.sigma2 ∧
    (S.gam * S.eta < 1 →
      S.sigma2 < S.mu / S.R - S.mu ^ 2 + (max (S.mu0 - S.mu) 0) ^ 2 + S.DeltaFin / S.R)

/-- Market thickness benefits the system in period `t` (p. 15): `V_t(M, D)` is (weakly)
increasing in `M > 0` for every fixed `D > 0`. -/
def Benefits (S : Sys Ω) (t : ℕ) : Prop :=
  ∀ D : ℝ, 0 < D → MonotoneOn (fun M => S.V t M D) (Set.Ioi 0)

/-- Market thickness is costly to the system in period `t` (p. 15): `V_t(M, D)` is (weakly)
decreasing in `M > 0` for every fixed `D > 0`. -/
def Costly (S : Sys Ω) (t : ℕ) : Prop :=
  ∀ D : ℝ, 0 < D → AntitoneOn (fun M => S.V t M D) (Set.Ioi 0)

/-- Market thickness is costly to the system in period `t` in the limit as `M → ∞`
(Theorem 1(c)): for every fixed `D > 0`, `V_t(M, D)` is (weakly) decreasing in `M` on a tail
`[M₀, ∞)`. -/
def CostlyInLimit (S : Sys Ω) (t : ℕ) : Prop :=
  ∀ D : ℝ, 0 < D → ∃ M₀ : ℝ, 0 < M₀ ∧ AntitoneOn (fun M => S.V t M D) (Set.Ici M₀)

/-- `∂₁V_t(M, D)`: the right partial derivative of `V_t` in `M` (Appendix A, Notation). -/
noncomputable def d1V (S : Sys Ω) (t : ℕ) (M D : ℝ) : ℝ :=
  derivWithin (fun M' => S.V t M' D) (Set.Ioi M) M

/-- `∂₂V_t(M, D)`: the right partial derivative of `V_t` in `D` (Appendix A, Notation). -/
noncomputable def d2V (S : Sys Ω) (t : ℕ) (M D : ℝ) : ℝ :=
  derivWithin (fun D' => S.V t M D') (Set.Ioi D) D

/-- The set in (14), p. 36:
`{y ∈ ℝ₊ : y ≥ (µ₀ − µ)M + (γδM/2p) E ∂₁V_{t+1}((ρ + δRβ)M + δRy, ηD + θM + ϵ)}`. -/
def yUset (S : Sys Ω) (t : ℕ) (M D : ℝ) : Set ℝ :=
  {y | 0 ≤ y ∧ (S.mu0 - S.mu) * M + S.gam * S.delta * M / (2 * S.p) *
      ∫ ω, S.d1V (t + 1) ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y)
        (S.eta * D + S.theta ω * M + S.eps ω) ∂S.P ≤ y}

/-- `y^U_t(M, D)` of (14), p. 36: the infimum of `yUset t M D`. -/
noncomputable def yU (S : Sys Ω) (t : ℕ) (M D : ℝ) : ℝ := sInf (S.yUset t M D)

/-- `L(t) := r Σ_{j=0}^{T−t} γ^j η^j` (Lemma 2(b), p. 37), for `t ≤ T + 1`. -/
noncomputable def Lfun (S : Sys Ω) (t : ℕ) : ℝ :=
  S.r * ∑ j ∈ Finset.range (S.T + 1 - t), (S.gam * S.eta) ^ j

/-- `G(t) := Σ_{i=0}^{T−t} γ^i(ρ + δRµ)^i (pµ̃ + γrµ_θ Σ_{j=0}^{T−t−1−i} γ^j η^j)` ((17), p. 37),
for integers `t ≤ T + 1`. -/
noncomputable def Gfun (S : Sys Ω) (t : ℤ) : ℝ :=
  ∑ i ∈ Finset.range ((S.T : ℤ) - t + 1).toNat,
    (S.gam * (S.rho + S.delta * S.R * S.mu)) ^ i *
      (S.p * S.muTilde + S.gam * S.r * S.muTheta *
        ∑ j ∈ Finset.range ((S.T : ℤ) - t - (i : ℤ)).toNat, (S.gam * S.eta) ^ j)

end Sys

end HybridOrderAlloc.Thickness


