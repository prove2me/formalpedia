-- Prove2me | Definitions.Def_VerticalOwnership_CheapTalk_Setting
-- name    : VerticalOwnership_CheapTalk_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:46.688934+00:00
-- url     : https://prove2.me/theorems/9b43a17e-e7ff-4664-a952-582d5fd45fd5
-- title:
--   §3, §5 — the PVO capacity model: demand μ_i + ε, profits (2)–(3), accounting payoff (4), z_s, z_r, K_L, K_H, conditions (12)–(13), β̳ (14), R(Δ) (15), the argument of (16)
-- statement:
--   This file fixes the supply-chain model of Avinadav and Shamir and the objects of their cheap-talk analysis.
--
--   **Primitives.** A retailer buys a component from a supplier. The supplier builds capacity $K$ at unit cost $c$; the retailer pays the wholesale price $w$ per unit delivered and sells at the retail price $r$. Demand in market state $i\in\{L,H\}$ is $D_i=\mu_i+\varepsilon$, where $\varepsilon$ is a random variable with law $P$, cumulative distribution function $F$ and lower support end $\underline{\varepsilon}$.
--
--   **Standing assumptions.** $P$ is a probability measure with a density (absolutely continuous with respect to Lebesgue measure); $\varepsilon$ is integrable with $\mathbb E[\varepsilon]=0$; $\underline{\varepsilon}<0$ and $F(\underline{\varepsilon})=0$; $F$ is strictly increasing on $\{x\ge\underline{\varepsilon}: F(x)<1\}$; $0<\mu_L<\mu_H$ and $\mu_L+\underline{\varepsilon}\ge 0$; $0<c<w<r$.
--
--   **Derived objects.** The quantile is $F^{-1}(z)=\inf\{x: z\le F(x)\}$. The critical fractiles are
--   $$z_s=1-\frac{c}{w},\qquad z_r=1-\frac{w}{r},$$
--   the information gap is $\Delta=\mu_H-\mu_L$, and the complete-information capacities are $K_L=\mu_L+F^{-1}(z_s)$ and $K_H=\mu_H+F^{-1}(z_s)$. For an advance order $q^{adv}$ and capacity $K$, the expected profits are
--   $$\pi_s(K\mid\mu_i,q^{adv})=\mathbb E\big[w\min(K,\max(\mu_i+\varepsilon,q^{adv}))-cK\big],$$
--   $$\pi_r(q^{adv},K\mid\mu_i)=\mathbb E\big[(r-w)\min(\mu_i+\varepsilon,K)-w\max(q^{adv}-\mu_i-\varepsilon,0)\big],$$
--   and the retailer's accounting payoff with ownership share $\beta$ is $v_r(q^{adv},K\mid\mu_i)=\pi_r(q^{adv},K\mid\mu_i)+\beta\,\pi_s(K\mid\mu_i,q^{adv})$. The supply-chain profit is $\pi_{sc}(K\mid\mu_i)=\pi_s(K\mid\mu_i,0)+\pi_r(0,K\mid\mu_i)$.
--
--   **Cheap-talk objects.** Condition (12) is $v_r(0,K_H\mid\mu_H)\ge v_r(0,K_L\mid\mu_H)$ and condition (13) is $v_r(0,K_L\mid\mu_L)\ge v_r(0,K_H\mid\mu_L)$. The threshold is
--   $$\underline{\underline{\beta}}=\frac{\pi_r(0,K_H\mid\mu_L)-\pi_r(0,K_L\mid\mu_L)}{\pi_s(K_L\mid\mu_L,0)-\pi_s(K_H\mid\mu_L,0)},$$
--   and, for $d>0$,
--   $$R(d)=\frac1d\int_{F^{-1}(z_s)}^{d+F^{-1}(z_s)}F(x)\,dx,\qquad \theta(\beta)=z_s+\frac{1-z_s}{1+\beta(1/z_r-1)}.$$
--
--   These definitions are shared by every statement of the mission; Theorem 2 and its milestones are claims about them.
--
--   **Formalization Note** The profits are Bochner integrals against $P$, not the closed forms the paper derives (those are milestones). $\underline{\underline{\beta}}$ is the plain quotient (the first expression of (14)); positivity of its denominator is a theorem, not part of the definition. $R(d)$ is only meaningful for $d>0$ (Lean's $1/0=0$). $\pi_{sc}$ is taken at $q^{adv}=0$, as in the proof of Proposition 1. The prior probability of the high state and the ownership share are not fields of the model: $\beta$ is an argument. Additions to the paper's assumptions: $c>0$, integrability of $\varepsilon$, and strict increase of $F$ on its support (the paper uses $F^{-1}$ as an inverse).
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), pp. 5–9 and 12–14, (1)–(4), (12)–(16)

import Mathlib

namespace VerticalOwnership.CheapTalk

open MeasureTheory ProbabilityTheory

/-- The primitives of the partial-vertical-ownership capacity model (§3, pp. 5–6):
capacity cost `c`, wholesale price `w`, retail price `r`, the two mean demands `μL < μH`,
the law `P` of the zero-mean demand noise `ε` (with CDF `F = cdf P`), and the lower end `εlo`
(ε̲) of the support of `ε`. -/
structure Model where
  c : ℝ
  w : ℝ
  r : ℝ
  μL : ℝ
  μH : ℝ
  P : Measure ℝ
  εlo : ℝ

namespace Model

/-- The standing assumptions of §3 (pp. 5–6), together with the disclosed additions
(`0 < c`, integrability of `ε`, strict increase of `F` on the support). -/
structure Standing (M : Model) : Prop where
  /-- `ε` is a random variable: its law is a probability measure. -/
  prob : IsProbabilityMeasure M.P
  /-- `ε` is integrable (presupposed by "zero-mean"). -/
  integrable : Integrable id M.P
  /-- `ε` has zero mean. -/
  mean_zero : ∫ x, x ∂M.P = 0
  /-- `ε` has a probability density function `f`. -/
  density : M.P ≪ volume
  /-- The lower end of the support is negative: `ε̲ < 0`. -/
  εlo_neg : M.εlo < 0
  /-- No mass at or below `ε̲`: `F(ε̲) = 0`. -/
  cdf_εlo : cdf M.P M.εlo = 0
  /-- `F` is strictly increasing on the support `{x ≥ ε̲ : F(x) < 1}`. -/
  strictMono : ∀ x y : ℝ, M.εlo ≤ x → x < y → cdf M.P x < 1 → cdf M.P x < cdf M.P y
  /-- `0 < μ_L`. -/
  μL_pos : 0 < M.μL
  /-- `μ_L < μ_H`. -/
  μL_lt_μH : M.μL < M.μH
  /-- Demand is non-negative: `μ_L + ε̲ ≥ 0`. -/
  demand_nonneg : 0 ≤ M.μL + M.εlo
  /-- `0 < c` (disclosed addition). -/
  c_pos : 0 < M.c
  /-- `c < w`. -/
  c_lt_w : M.c < M.w
  /-- `w < r`. -/
  w_lt_r : M.w < M.r

/-- The quantile function `F⁻¹(z) = inf {x : z ≤ F(x)}`; used only at `z ∈ (0, 1)`. -/
noncomputable def Finv (M : Model) (z : ℝ) : ℝ := sInf {x : ℝ | z ≤ cdf M.P x}

/-- The supplier's critical fractile `z_s = 1 − c/w` ((2), p. 8). -/
noncomputable def zs (M : Model) : ℝ := 1 - M.c / M.w

/-- The retailer's critical fractile `z_r = 1 − w/r` ((11), p. 11). -/
noncomputable def zr (M : Model) : ℝ := 1 - M.w / M.r

/-- The information gap `Δ = μ_H − μ_L` (p. 6). -/
def Δ (M : Model) : ℝ := M.μH - M.μL

/-- The supplier's complete-information capacity in the low state, `K_L = μ_L + F⁻¹(z_s)`. -/
noncomputable def KL (M : Model) : ℝ := M.μL + M.Finv M.zs

/-- The supplier's complete-information capacity in the high state, `K_H = μ_H + F⁻¹(z_s)`. -/
noncomputable def KH (M : Model) : ℝ := M.μH + M.Finv M.zs

/-- The supplier's expected profit `π_s(K | μ, q^adv) = E[w min(K, max(μ + ε, q^adv)) − cK]`
((2), first line, p. 8). Arguments: mean demand `μ`, advance order `q`, capacity `K`. -/
noncomputable def πs (M : Model) (μ q K : ℝ) : ℝ :=
  ∫ ε, (M.w * min K (max (μ + ε) q) - M.c * K) ∂M.P

/-- The retailer's expected operational profit
`π_r(q^adv, K | μ) = E[(r − w) min(μ + ε, K) − w max(q^adv − μ − ε, 0)]` ((3), first line, p. 8).
Arguments: mean demand `μ`, advance order `q`, capacity `K`. -/
noncomputable def πr (M : Model) (μ q K : ℝ) : ℝ :=
  ∫ ε, ((M.r - M.w) * min (μ + ε) K - M.w * max (q - μ - ε) 0) ∂M.P

/-- The retailer's accounting payoff `v_r(q^adv, K | μ) = π_r(q^adv, K | μ) + β π_s(K | μ, q^adv)`
((4), first line, p. 9). Arguments: ownership share `β`, mean demand `μ`, advance order `q`,
capacity `K`. -/
noncomputable def vr (M : Model) (β μ q K : ℝ) : ℝ :=
  M.πr μ q K + β * M.πs μ q K

/-- The supply chain's expected profit `π_sc(K | μ) = π_s(K | μ, 0) + π_r(0, K | μ)` (p. 8),
taken at `q^adv = 0` as in Proposition 1 (p. 15). -/
noncomputable def πsc (M : Model) (μ K : ℝ) : ℝ :=
  M.πs μ 0 K + M.πr μ 0 K

/-- Condition (12), p. 12: the high type does not gain by reporting low,
`v_r(0, μ_H + F⁻¹(z_s) | μ_H) ≥ v_r(0, μ_L + F⁻¹(z_s) | μ_H)`. -/
def cond12 (M : Model) (β : ℝ) : Prop :=
  M.vr β M.μH 0 M.KL ≤ M.vr β M.μH 0 M.KH

/-- Condition (13), p. 12: the low type does not gain by reporting high,
`v_r(0, μ_L + F⁻¹(z_s) | μ_L) ≥ v_r(0, μ_H + F⁻¹(z_s) | μ_L)`. -/
def cond13 (M : Model) (β : ℝ) : Prop :=
  M.vr β M.μL 0 M.KH ≤ M.vr β M.μL 0 M.KL

/-- The cheap-talk threshold `β̳`, the first expression of (14), p. 13:
`[π_r(0, K_H | μ_L) − π_r(0, K_L | μ_L)] / [π_s(K_L | μ_L, 0) − π_s(K_H | μ_L, 0)]`. -/
noncomputable def betaCT (M : Model) : ℝ :=
  (M.πr M.μL 0 M.KH - M.πr M.μL 0 M.KL) / (M.πs M.μL 0 M.KL - M.πs M.μL 0 M.KH)

/-- `R(d) = (1/d) ∫_{F⁻¹(z_s)}^{d + F⁻¹(z_s)} F(x) dx` ((15), p. 13), as a function of the
gap `d`; meaningful for `d > 0`. -/
noncomputable def R (M : Model) (d : ℝ) : ℝ :=
  (1 / d) * ∫ x in M.Finv M.zs..d + M.Finv M.zs, cdf M.P x

/-- The argument of `R⁻¹` in (16), p. 14: `θ(β) = z_s + (1 − z_s) / (1 + β (1/z_r − 1))`. -/
noncomputable def theta (M : Model) (β : ℝ) : ℝ :=
  M.zs + (1 - M.zs) / (1 + β * (1 / M.zr - 1))

end Model

end VerticalOwnership.CheapTalk


