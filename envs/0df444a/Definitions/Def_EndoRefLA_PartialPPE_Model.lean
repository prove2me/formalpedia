-- Prove2me | Definitions.Def_EndoRefLA_PartialPPE_Model
-- name    : EndoRefLA_PartialPPE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:07.722412+00:00
-- url     : https://prove2.me/theorems/6f4c6864-3c83-45cf-9756-f6a27e95eb7c
-- title:
--   §2.1–§3.1, pp. 8–19 — complete market, De Giorgi–Post preference V_λ(X|B), Assumption 1, problem (4), λmax (6), PE/PPE and Y(B0, c0)
-- statement:
--   This file sets up the one-period complete-market model of He and Strub (§2.1–§2.3 and §3.1).
--
--   **Market.** Prospects are nonnegative random variables $X$ on a probability space $(\Omega,\mathcal F,P)$. The pricing kernel $\rho$ is a positive integrable random variable, and the price of $X$ is $\mathbb E[\rho X]\in[0,\infty]$. An agent with initial wealth $x_0$ can afford the set
--   $$\mathcal X(x_0)=\{X \mid X \text{ is } \mathcal F\text{-measurable},\ \mathbb E[\rho X]\le x_0,\ X\ge 0\}.$$
--
--   **Utility (Assumption 1).** $u$ is finite, strictly increasing, strictly concave and continuously differentiable on $(0,\infty)$, with $u(0)=\lim_{x\downarrow 0}u(x)\in[-\infty,\infty)$, the Inada conditions $u'(0+)=+\infty$, $u'(+\infty)=0$, and $\mathbb E|\rho\,(u')^{-1}(\nu\rho)|<\infty$, $\mathbb E|u((u')^{-1}(\nu\rho))|<\infty$ for every $\nu>0$. The inverse marginal utility $(u')^{-1}(y)$ is the unique $x>0$ with $u'(x)=y$, for $y>0$.
--
--   **Preferences.** With the expectation convention $\mathbb E[Y]=-\infty$ whenever $\mathbb E|Y|=+\infty$, the preference value of a prospect $X$ given a reference point $B$ is
--   $$V_\lambda(X\mid B)=\mathbb E[u(X)]+\alpha\,\mathbb E\big[\mu(u(X)-u(B))\big],\qquad \mu(z)=z\mathbf 1_{\{z\ge 0\}}+\lambda z\mathbf 1_{\{z<0\}},$$
--   with $\alpha>0$ and degree of loss aversion $\lambda\ge1$. Admissible reference points $B$ are measurable, nonnegative, and satisfy $\mathbb E|u(B)|<\infty$.
--
--   **Objects defined.**
--   1. Optimality for problem (4): $X$ maximizes $V_\Lambda(\cdot\mid B_0)$ over $\mathcal X(x_0)$.
--   2. The candidate solution (5) for a multiplier $\nu$: $(u')^{-1}(\nu\rho)$ where $\rho<\frac1\nu u'(B_0)$; $B_0$ where $\frac1\nu u'(B_0)\le\rho\le\frac{1+\alpha\Lambda}{1+\alpha}\frac1\nu u'(B_0)$; $(u')^{-1}\big(\frac{1+\alpha}{1+\alpha\Lambda}\nu\rho\big)$ otherwise.
--   3. $\bar z=\operatorname{esssup}(u'(B_0)/\rho)\in(0,\infty]$, $\underline z=\operatorname{essinf}(u'(B_0)/\rho)\in[0,\infty)$, and $\lambda_{\max}\in[1,+\infty]$ of (6), built from the multipliers $\nu_G$, $\nu_L$; also $\lambda\wedge\lambda_{\max}$.
--   4. Personal equilibrium (PE) and preferred personal equilibrium (PPE) within a choice set $S$: $X\in S$ with $V_\lambda(X\mid X)\ge V_\lambda(Y\mid X)$ for all $Y\in S$; a PPE is a PE with the largest $V_\lambda(X\mid X)$ among PEs.
--   5. The choice set (9) under a maximum mental cost $c_0$: $\mathcal Y(B_0,c_0)=\{X\in\mathcal X(x_0): f_{B_0}(V_\lambda(X\mid B_0))\le c_0\}$.
--   6. The map $\eta\mapsto\Lambda(\eta)=\frac1\alpha\Big((1+\alpha)\frac{1+(1+\alpha\lambda)\eta}{1+(1+\alpha)\eta}-1\Big)$ of (19).
--
--   These are the objects of Theorems 1–3 and Proposition 1.
--
--   **Formalization Note.** Expectations of utilities are extended reals ($\bot=-\infty$), computed by `Ex`, which returns the integral only for a.s. finite integrable integrands. The price $\mathbb E[\rho X]$ is a lower Lebesgue integral in $[0,\infty]$. The utility of wealth $0$ is the parameter `u0`, so log utility ($u(0)=-\infty$) is covered. Where $B_0=0$, $u'(B_0)=+\infty$ is handled by an explicit branch. $\lambda_{\max}$ takes $\nu_G,\nu_L$ as arguments; theorems assume they are the roots that (6) describes. The paper never states the domain of $f_{B_0}$; here $f:\mathbb R\to\mathbb R$, and a prospect with $V_\lambda(X\mid B_0)=-\infty$ is not in $\mathcal Y(B_0,c_0)$. A PE candidate is required to be an admissible reference point ($\mathbb E|u(X)|<\infty$), per the standing restriction on p. 9.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), pp. 8–19 (PDF 8–19), §2.1–§2.3, §3.1, (1)–(2), Assumption 1, (4)–(6), (9)–(10); (19) on p. 34

import Mathlib

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The pricing kernel, p. 8: "a positive, integrable random variable" `ρ`; the price of a
prospect `X` is `E[ρX]`. -/
def IsPricingKernel (P : Measure Ω) (ρ : Ω → ℝ) : Prop :=
  Measurable ρ ∧ (∀ ω, 0 < ρ ω) ∧ Integrable ρ P

/-- `(u′)⁻¹`, the inverse marginal utility: `Iinv u y = inf {x > 0 : u′(x) ≤ y}`. Under
Assumption 1, `u′` is a continuous strictly decreasing bijection of `(0, ∞)` onto itself, so for
`y > 0` this is the unique `x > 0` with `u′(x) = y`. Values at `y ≤ 0` are never used. -/
noncomputable def Iinv (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf {x | 0 < x ∧ deriv u x ≤ y}

/-- **Assumption 1**, p. 9. `u` is finite, strictly increasing, strictly concave and continuously
differentiable on `(0, ∞)`; `u0 = u(0) = lim_{x↓0} u(x) ∈ [−∞, ∞)`; the Inada conditions
`lim_{x↓0} u′(x) = +∞`, `lim_{x↑∞} u′(x) = 0`; and `E|ρ (u′)⁻¹(νρ)| < ∞`,
`E|u((u′)⁻¹(νρ))| < ∞` for every `ν > 0`. Values of `u` on `(−∞, 0]` are not used: the
utility of the wealth level `0` is `u0` (see `uE`). -/
structure Assumption1 (P : Measure Ω) (ρ : Ω → ℝ) (u : ℝ → ℝ) (u0 : EReal) : Prop where
  strictMonoOn : StrictMonoOn u (Set.Ioi 0)
  strictConcaveOn : StrictConcaveOn ℝ (Set.Ioi 0) u
  contDiffOn : ContDiffOn ℝ 1 u (Set.Ioi 0)
  tendsto_zero : Tendsto (fun x => (u x : EReal)) (𝓝[>] 0) (𝓝 u0)
  u0_ne_top : u0 ≠ ⊤
  inada_zero : Tendsto (deriv u) (𝓝[>] 0) atTop
  inada_top : Tendsto (deriv u) atTop (𝓝 0)
  integrable_budget : ∀ ν : ℝ, 0 < ν → Integrable (fun ω => ρ ω * Iinv u (ν * ρ ω)) P
  integrable_utility : ∀ ν : ℝ, 0 < ν → Integrable (fun ω => u (Iinv u (ν * ρ ω))) P

/-- The utility `u : [0, ∞) → ℝ ∪ {−∞}` of a wealth level `x ≥ 0`, as an extended real:
`u(x)` for `x > 0` and `u(0) = u0` at `x = 0` (also returned, harmlessly, for `x < 0`, which
no prospect takes). -/
noncomputable def uE (u : ℝ → ℝ) (u0 : EReal) (x : ℝ) : EReal :=
  if 0 < x then (u x : EReal) else u0

/-- The gain-loss function `µ(z) = z 1{z ≥ 0} + λ z 1{z < 0}` of (2), on extended reals
(so `µ(−∞) = −∞` and `µ(+∞) = +∞` for `λ > 0`). -/
noncomputable def gl (lam : ℝ) (z : EReal) : EReal :=
  if 0 ≤ z then z else (lam : EReal) * z

/-- The expectation with the convention of p. 9: "set `E[Y] = −∞` for any `Y` such that
`E[|Y|] = +∞`". `Ex P Y` is the integral of `Y` when `Y` is a.s. finite and integrable, and
`⊥ = −∞` otherwise. It never takes the value `⊤`. -/
noncomputable def Ex (P : Measure Ω) (Y : Ω → EReal) : EReal :=
  if (∀ᵐ ω ∂P, Y ω ≠ ⊥ ∧ Y ω ≠ ⊤) ∧ Integrable (fun ω => (Y ω).toReal) P
  then ((∫ ω, (Y ω).toReal ∂P : ℝ) : EReal) else ⊥

/-- The De Giorgi–Post preference value (1), p. 9, of a prospect `X` given a reference point
`B`, with degree of loss aversion `lam`:
`V_λ(X|B) = E[u(X)] + α E[µ(u(X) − u(B))]` (state-dependent evaluation). -/
noncomputable def V (P : Measure Ω) (α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (lam : ℝ)
    (X B : Ω → ℝ) : EReal :=
  Ex P (fun ω => uE u u0 (X ω)) +
    (α : EReal) * Ex P (fun ω => gl lam (uE u u0 (X ω) - uE u u0 (B ω)))

/-- The price `E[ρX]` of a nonnegative prospect `X`, in `[0, ∞]` (a lower Lebesgue integral, so
an unaffordable prospect has price `+∞`, never a junk `0`). -/
noncomputable def price (P : Measure Ω) (ρ : Ω → ℝ) (X : Ω → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (ρ ω * X ω) ∂P

/-- `X(x0)`, p. 15, the feasible set of (4): `X` is `F`-measurable, `X ≥ 0` and `E[ρX] ≤ x0`. -/
def Feasible (P : Measure Ω) (ρ : Ω → ℝ) (x0 : ℝ) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ price P ρ X ≤ ENNReal.ofReal x0

/-- An admissible reference point, p. 9 ("we always restrict ourselves to reference points `B`
such that `E[|u(B)|] < +∞`"): a measurable nonnegative `B` with `E|u(B)| < ∞`. -/
def IsRefPoint (P : Measure Ω) (u : ℝ → ℝ) (u0 : EReal) (B : Ω → ℝ) : Prop :=
  Measurable B ∧ (∀ ω, 0 ≤ B ω) ∧ Ex P (fun ω => uE u u0 (B ω)) ≠ ⊥

/-- `X` is an optimal solution of problem (4), p. 12, for the reference point `B0` and the
degree of loss aversion `Λ`: `X` maximizes `V_Λ(·|B0)` over `X(x0)`. -/
def IsOptEx (P : Measure Ω) (ρ : Ω → ℝ) (x0 α : ℝ) (u : ℝ → ℝ) (u0 : EReal)
    (B0 : Ω → ℝ) (Λ : ℝ) (X : Ω → ℝ) : Prop :=
  Feasible P ρ x0 X ∧ ∀ Y, Feasible P ρ x0 Y → V P α u u0 Λ Y B0 ≤ V P α u u0 Λ X B0

/-- The right-hand side of (5), p. 12, for a multiplier `ν` and a degree of loss aversion `Λ`:
`(u′)⁻¹(νρ)` if `ρ < u′(B0)/ν`; `B0` if `u′(B0)/ν ≤ ρ ≤ ((1+αΛ)/(1+α)) u′(B0)/ν`;
`(u′)⁻¹(((1+α)/(1+αΛ)) νρ)` otherwise. Where `B0 = 0`, `u′(B0) = +∞` (Inada), so the first
case applies. -/
noncomputable def Xhat (ρ : Ω → ℝ) (α : ℝ) (u : ℝ → ℝ) (B0 : Ω → ℝ) (ν Λ : ℝ) (ω : Ω) : ℝ :=
  if B0 ω = 0 ∨ ρ ω < deriv u (B0 ω) / ν then Iinv u (ν * ρ ω)
  else if ρ ω ≤ (1 + α * Λ) / (1 + α) * (deriv u (B0 ω) / ν) then B0 ω
  else Iinv u ((1 + α) / (1 + α * Λ) * ν * ρ ω)

/-- The random variable `u′(B0)/ρ` in `(0, +∞]`, equal to `+∞` where `B0 = 0`. -/
noncomputable def margRatio (ρ : Ω → ℝ) (u : ℝ → ℝ) (B0 : Ω → ℝ) (ω : Ω) : EReal :=
  if B0 ω = 0 then ⊤ else ((deriv u (B0 ω) / ρ ω : ℝ) : EReal)

/-- `z̄ := esssup (u′(B0)/ρ) ∈ (0, +∞]`, p. 14. -/
noncomputable def zbar (P : Measure Ω) (ρ : Ω → ℝ) (u : ℝ → ℝ) (B0 : Ω → ℝ) : EReal :=
  essSup (margRatio ρ u B0) P

/-- `z̲ := essinf (u′(B0)/ρ) ∈ [0, +∞)`, p. 14. -/
noncomputable def zlow (P : Measure Ω) (ρ : Ω → ℝ) (u : ℝ → ℝ) (B0 : Ω → ℝ) : EReal :=
  essInf (margRatio ρ u B0) P

/-- `λmax ∈ [1, +∞]` of (6), p. 14:
* `max(((1+α)(νG/z̲) − 1)/α, 1)` if `E[ρB0] < x0`;
* `max(((1+α)(z̄/νL) − 1)/α, 1)` if `E[ρB0] > x0`;
* `((1+α)(z̄/z̲) − 1)/α` if `E[ρB0] = x0`;

where `νG`, `νL > 0` solve `E[ρ((u′)⁻¹(νGρ) ∨ B0)] = x0`, resp. `E[ρ((u′)⁻¹(νLρ) ∧ B0)] = x0`
(they are passed as arguments; theorems assume they are such roots). The infinite cases are
explicit: `νG/0 = z̄/νL = +∞` (for `z̄ = +∞`) and `z̄/0 = +∞` give `λmax = +∞`; `νG/(+∞) = 0`
(`z̲ = +∞`, i.e. `B0 = 0` a.s.) gives `max(−1/α, 1) = 1`. In the case `E[ρB0] = x0 > 0`,
`B0 > 0` on a non-null set, so `z̲ < +∞`, and `z̄ = +∞` gives `+∞`. -/
noncomputable def lamMax (P : Measure Ω) (ρ : Ω → ℝ) (x0 α : ℝ) (u : ℝ → ℝ) (B0 : Ω → ℝ)
    (νG νL : ℝ) : EReal :=
  if price P ρ B0 < ENNReal.ofReal x0 then
    (if zlow P ρ u B0 = 0 then ⊤
     else if zlow P ρ u B0 = ⊤ then ((max (-1 / α) 1 : ℝ) : EReal)
     else ((max (((1 + α) * (νG / (zlow P ρ u B0).toReal) - 1) / α) 1 : ℝ) : EReal))
  else if ENNReal.ofReal x0 < price P ρ B0 then
    (if zbar P ρ u B0 = ⊤ then ⊤
     else ((max (((1 + α) * ((zbar P ρ u B0).toReal / νL) - 1) / α) 1 : ℝ) : EReal))
  else
    (if zbar P ρ u B0 = ⊤ ∨ zlow P ρ u B0 = 0 then ⊤
     else ((((1 + α) * ((zbar P ρ u B0).toReal / (zlow P ρ u B0).toReal) - 1) / α : ℝ) :
       EReal))

/-- `λ ∧ λmax` as a real number: `λ` when `λmax = +∞`, else `min λ λmax`. -/
noncomputable def lamCap (P : Measure Ω) (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ)
    (B0 : Ω → ℝ) (νG νL : ℝ) : ℝ :=
  if lamMax P ρ x0 α u B0 νG νL = ⊤ then lam
  else min lam (lamMax P ρ x0 α u B0 νG νL).toReal

/-- A personal equilibrium within a choice set `S` (p. 15 for `S = X(x0)`, p. 19 for
`S = Y(B0, c0)`): `X ∈ S`, `X` is an admissible reference point, and `V_λ(X|X) ≥ V_λ(Y|X)`
for all `Y ∈ S`. -/
def IsPEin (P : Measure Ω) (α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (lam : ℝ)
    (S : Set (Ω → ℝ)) (X : Ω → ℝ) : Prop :=
  X ∈ S ∧ IsRefPoint P u u0 X ∧ ∀ Y ∈ S, V P α u u0 lam Y X ≤ V P α u u0 lam X X

/-- A preferred personal equilibrium within `S`: a PE within `S` with
`V_λ(X|X) ≥ V_λ(Z|Z)` for every PE `Z` within `S`. -/
def IsPPEin (P : Measure Ω) (α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (lam : ℝ)
    (S : Set (Ω → ℝ)) (X : Ω → ℝ) : Prop :=
  IsPEin P α u u0 lam S X ∧
    ∀ Z, IsPEin P α u u0 lam S Z → V P α u u0 lam Z Z ≤ V P α u u0 lam X X

/-- `Y(B0, c0)` of (9), p. 18: feasible prospects whose mental cost `f_B0(V_λ(X|B0))` is at most
`c0`. `f : ℝ → ℝ` is the mental cost function; a prospect with `V_λ(X|B0) = −∞` is not
admissible (the domain of `f_B0` is not stated in the paper; disclosed convention). -/
def Ycal (P : Measure Ω) (ρ : Ω → ℝ) (x0 α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (lam : ℝ)
    (B0 : Ω → ℝ) (f : ℝ → ℝ) (c0 : ℝ) : Set (Ω → ℝ) :=
  {X | Feasible P ρ x0 X ∧ ∃ v : ℝ, V P α u u0 lam X B0 = v ∧ f v ≤ c0}

/-- `Λ` of (19), p. 34, as a function of the multiplier `η`:
`Λ(η) = (1/α)((1+α)(1+(1+αλ)η)/(1+(1+α)η) − 1)`. -/
noncomputable def LamEta (α lam η : ℝ) : ℝ :=
  (1 / α) * ((1 + α) * (1 + (1 + α * lam) * η) / (1 + (1 + α) * η) - 1)

end EndoRefLA.PartialPPE


