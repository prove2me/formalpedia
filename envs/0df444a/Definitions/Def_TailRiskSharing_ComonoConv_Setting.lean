-- Prove2me | Definitions.Def_TailRiskSharing_ComonoConv_Setting
-- name    : TailRiskSharing_ComonoConv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:30.08379+00:00
-- url     : https://prove2.me/theorems/2740fc3b-a963-43c0-affe-baec3cadabf3
-- title:
--   §2.1–2.4, pp. 5–8 — atomless P, F_X, left/right VaR, quantile uniform U_X, tail equivalence (6), risk-measure properties, tail risk measures (Def. 1), allocations (4), inf-convolution (5)
-- statement:
--   The common setting of the paper. Fix a probability space $(\Omega,\mathcal F,\mathbb P)$ which is **atomless**: every measurable set $A$ with $\mathbb P(A)>0$ contains a measurable $B\subseteq A$ with $0<\mathbb P(B)<\mathbb P(A)$. The domain of risk measures is $L^0$, the set of all real random variables. A positive value of $X$ is a loss.
--
--   1. The **distribution function** of $X$ is $F_X(x)=\mathbb P(X\le x)$.
--   2. For a level $\alpha$, the **left** and **right Value-at-Risk** are
--   $$\mathrm{VaR}^L_\alpha(X)=\inf\{x\in\mathbb R: F_X(x)\ge 1-\alpha\},\qquad \mathrm{VaR}^R_\alpha(X)=\inf\{x\in\mathbb R: F_X(x)> 1-\alpha\}.$$
--      The left-continuous quantile function is $F^{-1}_X(p)=\mathrm{VaR}^L_{1-p}(X)$ for $p\in(0,1]$.
--   3. A **quantile uniform** of $X$ is a random variable $U_X$, uniformly distributed on $[0,1]$, with $F_X^{-1}(U_X)=X$ almost surely.
--   4. For $p\in(0,1]$ the tail $X_p=F_X^{-1}(1-p+pU_X)$ has distribution function $(F_X(x)-(1-p))_+/p$, display (6). Accordingly, $X_p\overset{d}{=}Y_p$ is encoded as $(F_X(x)-(1-p))_+=(F_Y(x)-(1-p))_+$ for all $x\in\mathbb R$.
--   5. A risk measure $\rho$ is **monotone** if $X\le Y$ a.s. implies $\rho(X)\le\rho(Y)$; **translation invariant** if $\rho(X-m)=\rho(X)-m$; **monetary** if both; **law invariant** if $F_X=F_Y$ implies $\rho(X)=\rho(Y)$.
--   6. (Definition 1) For $p\in(0,1)$, $\rho$ is a **$p$-tail risk measure** if $\rho(X)=\rho(Y)$ whenever $X_p\overset{d}{=}Y_p$.
--   7. The **allocations** of $X$ among $n$ agents are $\mathbb A_n(X)=\{(X_1,\dots,X_n)\in (L^0)^n: \sum_{i=1}^n X_i=X\}$, (4), and the **inf-convolution** of $\rho_1,\dots,\rho_n$ is
--   $$\mathop{\square}_{i=1}^n\rho_i(X)=\inf\Big\{\sum_{i=1}^n\rho_i(X_i):(X_1,\dots,X_n)\in\mathbb A_n(X)\Big\}\in[-\infty,\infty],$$
--      display (5). An allocation attaining the infimum is **optimal**.
--
--   These objects are shared by every mission of this series on the paper.
--
--   **Formalization Note** Random variables are functions $\Omega\to\mathbb R$; $L^0$ is the set of measurable ones. The sum constraint in $\mathbb A_n(X)$ is pointwise. The inf-convolution is valued in extended reals, so an empty or unbounded-below set of aggregate values gives $+\infty$ or $-\infty$ rather than a junk real. Risk measures of individual agents are real valued, as in §2.3.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 5–8, §2.1–2.4, (4)–(6), Definition 1

import Mathlib

namespace TailRiskSharing.ComonoConv

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.1 p. 5: atomless (classical sense; Mathlib's `NoAtoms` is only "singletons are null"). -/
def IsAtomless (P : Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < P s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < P t ∧ P t < P s

/-- §2.1 p. 5: distribution function `F_X(x) = P(X ≤ x)`. -/
noncomputable def distFn (P : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ := P.real {ω | X ω ≤ x}

/-- §2.2 p. 6: left VaR, `VaR^L_α(X) = inf {x | F_X(x) ≥ 1 - α}` (small-α convention). -/
noncomputable def VaRL (P : Measure Ω) (α : ℝ) (X : Ω → ℝ) : ℝ := sInf {x | 1 - α ≤ distFn P X x}

/-- §2.2 p. 6: right VaR, `VaR^R_α(X) = inf {x | F_X(x) > 1 - α}`. -/
noncomputable def VaRR (P : Measure Ω) (α : ℝ) (X : Ω → ℝ) : ℝ := sInf {x | 1 - α < distFn P X x}

/-- §2.1 p. 5: the domain `L⁰` of all random variables (measurable real functions). -/
def L0 : Set (Ω → ℝ) := {X | Measurable X}

/-- §2.1 p. 5: `U` is a uniform random variable on `[0, 1]` with `F⁻¹_X(U) = X` a.s.
(`F⁻¹_X(p) = VaR^L_{1-p}(X)`). -/
def IsQuantileUniform (P : Measure Ω) (X U : Ω → ℝ) : Prop :=
  Measurable U ∧ P.map U = volume.restrict (Set.Icc (0:ℝ) 1) ∧
    ∀ᵐ ω ∂P, VaRL P (1 - U ω) X = X ω

/-- (6) p. 8: `X_p =d Y_p`, encoded through the distribution function of the tail,
`p · P(X_p ≤ x) = (F_X(x) - (1 - p))⁺`. -/
def TailEquiv (P : Measure Ω) (p : ℝ) (X Y : Ω → ℝ) : Prop :=
  ∀ x : ℝ, max (distFn P X x - (1 - p)) 0 = max (distFn P Y x - (1 - p)) 0

/-- §2.2 p. 5: monotone on the domain `dom`. -/
def IsMonotone (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ᵐ ω ∂P, X ω ≤ Y ω) → ρ X ≤ ρ Y

/-- §2.2 p. 5: translation invariant on the domain `dom`. -/
def IsTranslationInvariant (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ m : ℝ, ρ (fun ω => X ω - m) = ρ X - m

/-- §2.2 p. 5: monetary = monotone and translation invariant. -/
def IsMonetary (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  IsMonotone P dom ρ ∧ IsTranslationInvariant dom ρ

/-- §2.2 p. 5: law invariant on the domain `dom`. -/
def IsLawInvariant (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ x, distFn P X x = distFn P Y x) → ρ X = ρ Y

/-- Definition 1, p. 8, through (6): `ρ` is a `p`-tail risk measure. -/
def IsTailRiskMeasure (P : Measure Ω) (dom : Set (Ω → ℝ)) (p : ℝ) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, TailEquiv P p X Y → ρ X = ρ Y

/-- (4) p. 7: the set `A_n(X)` of allocations of `X` (pointwise sum). -/
def Allocations (dom : Set (Ω → ℝ)) (n : ℕ) (X : Ω → ℝ) : Set (Fin n → Ω → ℝ) :=
  {Xs | (∀ i, Xs i ∈ dom) ∧ ∀ ω, ∑ i, Xs i ω = X ω}

/-- (5) p. 7: the inf-convolution `□ ρᵢ`, valued in `EReal`. -/
noncomputable def infConv (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) :
    EReal :=
  ⨅ Xs ∈ Allocations dom n X, ((∑ i, ρ i (Xs i) : ℝ) : EReal)

/-- p. 7: an optimal allocation of `X` for `(ρ₁, …, ρₙ)`. -/
def IsOptimalAllocation (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ)
    (Xs : Fin n → Ω → ℝ) : Prop :=
  Xs ∈ Allocations dom n X ∧ ((∑ i, ρ i (Xs i) : ℝ) : EReal) = infConv dom ρ X

end TailRiskSharing.ComonoConv


