-- Prove2me | Definitions.Def_ConvexRiskFn_Order_Setting
-- name    : ConvexRiskFn_Order_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:50.017125+00:00
-- url     : https://prove2.me/theorems/080dcc10-f871-4ccf-8ba2-08029c039601
-- title:
--   §5.1–§5.2, pp. 443–446 — risk functions on L_p, Definitions 5.1–5.2, (A2), the usual stochastic order, consistency, the uniform random variable, cdf and its inverse
-- statement:
--   This file fixes the objects of §5.1–§5.2 of Ruszczyński and Shapiro, *Optimization of convex risk functions*. Throughout, $(\Omega,\mathcal F,P)$ is a probability space, $p\in[1,\infty)$, and the space of random outcomes is $\mathcal X=\mathcal L_p(\Omega,\mathcal F,P)$. Smaller outcomes are better (an outcome is a cost), and a **risk function** is a map $\rho:\mathcal X\to\mathbb R$.
--
--   1. A **uniform random variable** is a measurable $U:\Omega\to\mathbb R$ with $P(U\le t)=t$ for all $t\in[0,1]$.
--   2. The **cdf** of $X$ is $F_X(t):=P(X\le t)$, and the **inverse** of a cdf $F$ is $F^{-1}(t):=\inf\{s: F(s)\ge t\}$.
--   3. $\rho$ is **distribution invariant** (Definition 5.2) if $\rho(X_1)=\rho(X_2)$ whenever $X_1,X_2\in\mathcal X$ satisfy $P(X_1\le t)=P(X_2\le t)$ for all $t\in\mathbb R$.
--   4. $\rho$ satisfies **(A2)** (monotonicity) if $X,Y\in\mathcal X$ and $X\le Y$ almost surely imply $\rho(X)\le\rho(Y)$.
--   5. $\rho$ is **risk averse** (Definition 5.1) if for every $\sigma$-algebra $\mathcal G\subset\mathcal F$, every $X\in\mathcal X$ and every version of the conditional expectation,
--   $$\rho(X)\ \ge\ \rho\big(\mathbb E[X\mid\mathcal G]\big).$$
--   6. The **usual stochastic order**: $X_2\succeq_{\mathrm{st}}X_1$ if $\mathbb E[u(X_2)]\ge\mathbb E[u(X_1)]$ for every nondecreasing $u:\mathbb R\to\mathbb R$ for which both expectations exist. The **increasing convex order** $X_2\succeq_{\mathrm{icx}}X_1$ is the same with $u$ ranging over the increasing convex functions; it is the published definition `StochasticOrders_MonotoneConvex_IcxOrder`.
--   7. $\rho$ is **consistent** with $\succeq_{\mathrm{st}}$ (resp. $\succeq_{\mathrm{icx}}$) if $X_2\succeq X_1$ implies $\rho(X_2)\ge\rho(X_1)$ for all $X_1,X_2\in\mathcal X$.
--
--   These are the objects of Lemma 5.1 and Theorem 5.1, which relate consistency with a stochastic order to monotonicity and risk aversion.
--
--   **Formalization Note** Elements of $\mathcal L_p$ are functions $\Omega\to\mathbb R$ with `MemLp X p P`, not almost-everywhere classes; every predicate quantifies only over such functions, so the values of $\rho$ elsewhere are irrelevant. The order of $\mathcal L_p$ in (A2) is the almost-sure order (p. 434). "The expectations exist" is integrability of $u\circ X_1$ and $u\circ X_2$, as in the published increasing convex order. A version of $\mathbb E[X\mid\mathcal G]$ is a $\mathcal G$-measurable function equal almost surely to Mathlib's `P[X|m]`. The real infimum in $F^{-1}$ is $0$ where the paper's value is $\pm\infty$, i.e. only for $t\notin(0,1)$.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 433 (A2), p. 434 (order of L_p), p. 443 §5.1 Definition 5.1 (5.1)–(5.2), p. 445 §5.2 Definition 5.2 and the usual stochastic order, p. 446 the increasing convex order

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder

namespace ConvexRiskFn.Order

open MeasureTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A uniform random variable on `(Ω, ℱ, P)` (Ruszczyński–Shapiro 2006, §5.2, p. 445): a measurable
`U : Ω → ℝ` with `P(U ≤ t) = t` for all `t ∈ [0, 1]`. -/
def IsUniformRV (P : Measure Ω) (U : Ω → ℝ) : Prop :=
  Measurable U ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, P {ω | U ω ≤ t} = ENNReal.ofReal t

/-- The cumulative distribution function `F_X(t) := P(X ≤ t)` of `X` (§5.2, p. 445). -/
noncomputable def cdfOf (P : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  (P {ω | X ω ≤ t}).toReal

/-- The inverse of a cdf, `F⁻¹(t) := inf {s : F(s) ≥ t}` (§5.2, p. 445). The real infimum is `0`
when the set is empty or unbounded below; for a cdf `F` this happens only for `t ∉ (0, 1)`, where the
paper's value is `±∞`. -/
noncomputable def cdfInv (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf {s : ℝ | t ≤ F s}

/-- Distribution invariance, Definition 5.2 (p. 445), on `𝒳 = ℒ_p(Ω, ℱ, P)`: if `X₁, X₂ ∈ 𝒳` and
`P(X₁ ≤ t) = P(X₂ ≤ t)` for all `t ∈ ℝ`, then `ρ(X₁) = ρ(X₂)`. -/
def DistInvariant (P : Measure Ω) (p : ENNReal) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X₁ X₂ : Ω → ℝ, MemLp X₁ p P → MemLp X₂ p P →
    (∀ t : ℝ, P {ω | X₁ ω ≤ t} = P {ω | X₂ ω ≤ t}) → ρ X₁ = ρ X₂

/-- Condition (A2), monotonicity (p. 433), on `𝒳 = ℒ_p(Ω, ℱ, P)` with its almost-everywhere order
(p. 434): if `X, Y ∈ 𝒳` and `Y ⪰ X`, i.e. `X ≤ Y` `P`-a.e., then `ρ(Y) ≥ ρ(X)`. -/
def A2 (P : Measure Ω) (p : ENNReal) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X Y : Ω → ℝ, MemLp X p P → MemLp Y p P → X ≤ᵐ[P] Y → ρ X ≤ ρ Y

/-- Risk aversion, Definition 5.1 (p. 443), on `𝒳 = ℒ_p(Ω, ℱ, P)`: for every σ-algebra `𝒢 ⊂ ℱ` and
every `X ∈ 𝒳`, `ρ(X) ≥ ρ(P_𝒢(X))` with `P_𝒢(X) = 𝔼[X | 𝒢]`, for every version of the conditional
expectation (§5.1, p. 443: "a considered property holds for every version of 𝔼[X | 𝒢]"). A version is
a `𝒢`-measurable function equal `P`-a.e. to Mathlib's `P[X|m]`. -/
def RiskAverse (P : Measure Ω) (p : ENNReal) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ m : MeasurableSpace Ω, m ≤ mΩ → ∀ X : Ω → ℝ, MemLp X p P →
    ∀ Y : Ω → ℝ, StronglyMeasurable[m] Y → Y =ᵐ[P] P[X|m] → ρ Y ≤ ρ X

/-- The usual stochastic order `X₂ ⪰_st X₁` (§5.2, p. 445), the integral stochastic order whose
generator is the set of all nondecreasing `u : ℝ → ℝ`: `𝔼[u(X₂)] ≥ 𝔼[u(X₁)]` for every nondecreasing
`u` for which both expectations exist. `StLE P X₁ X₂` reads `X₁ ⪯_st X₂`. -/
def StLE (P : Measure Ω) (X₁ X₂ : Ω → ℝ) : Prop :=
  ∀ u : ℝ → ℝ, Monotone u → Integrable (u ∘ X₁) P → Integrable (u ∘ X₂) P →
    ∫ ω, u (X₁ ω) ∂P ≤ ∫ ω, u (X₂ ω) ∂P

/-- Consistency with the usual stochastic order (§5.2, p. 445): `X₂ ⪰_st X₁` implies
`ρ(X₂) ≥ ρ(X₁)` for all `X₁, X₂ ∈ 𝒳 = ℒ_p(Ω, ℱ, P)`. -/
def ConsistentSt (P : Measure Ω) (p : ENNReal) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X₁ X₂ : Ω → ℝ, MemLp X₁ p P → MemLp X₂ p P → StLE P X₁ X₂ → ρ X₁ ≤ ρ X₂

/-- Consistency with the increasing convex order (§5.2, p. 446): `X₂ ⪰_icx X₁` implies
`ρ(X₂) ≥ ρ(X₁)` for all `X₁, X₂ ∈ 𝒳 = ℒ_p(Ω, ℱ, P)`. The order is the published
`StochasticOrders.MonotoneConvex.IcxOrder` with both variables on `(Ω, P)`. -/
def ConsistentIcx (P : Measure Ω) (p : ENNReal) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X₁ X₂ : Ω → ℝ, MemLp X₁ p P → MemLp X₂ p P →
    StochasticOrders.MonotoneConvex.IcxOrder P P X₁ X₂ → ρ X₁ ≤ ρ X₂

end ConvexRiskFn.Order


