-- Prove2me | Definitions.Def_TailRiskSharing_VaRTail_Setting
-- name    : TailRiskSharing_VaRTail_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:07.568448+00:00
-- url     : https://prove2.me/theorems/c292404b-35da-4589-84d8-2b65e8ffc6d2
-- title:
--   §2.1–2.4, pp. 5–8, and Theorem 2, p. 13 — U_X, tail equivalence (6), monetary, law-invariant and tail risk measures (Definition 1), X^[α]
-- statement:
--   This file fixes the risk-measure vocabulary of §2.1–2.4 of Liu, Mao, Wang and Wei and the truncated position $X^{[\alpha]}$ of their Theorem 2. It builds on the distribution function $F_X$ and the VaRs $\mathrm{VaR}^L_\alpha$, $\mathrm{VaR}^R_\alpha$ of the basic setting. Write $F^{-1}_X(p)=\mathrm{VaR}^L_{1-p}(X)$, the left-continuous quantile, for $p\in(0,1]$.
--
--   1. **Quantile uniform.** A random variable $U$ is a *quantile uniform* of $X$ (the paper's $U_X$) if $U$ is measurable, uniformly distributed on $[0,1]$, and $F^{-1}_X(U)=X$ almost surely.
--   2. **Tails.** For $p\in(0,1]$, the tail $X_p=F^{-1}_X(1-p+pU_X)$ has distribution function $(F_X(x)-(1-p))_+/p$, display (6). Accordingly "$X_p\overset{d}{=}Y_p$" is the condition
--   $$(F_X(x)-(1-p))_+=(F_Y(x)-(1-p))_+\quad\text{for all }x\in\mathbb R.$$
--   3. **Properties of risk measures** on a domain $\mathcal X$. A risk measure $\rho$ is *monotone* if $\rho(X)\le\rho(Y)$ for all $X,Y\in\mathcal X$ with $X\le Y$ a.s.; *translation-invariant* if $\rho(X-m)=\rho(X)-m$ for all $m\in\mathbb R$ and $X\in\mathcal X$; *monetary* if both hold; *law-invariant* if $\rho(X)=\rho(Y)$ whenever $F_X=F_Y$; and (Definition 1) a **$p$-tail risk measure** if $\rho(X)=\rho(Y)$ for all $X,Y\in\mathcal X$ with $X_p\overset{d}{=}Y_p$.
--   4. The same notions of monotone, translation-invariant, monetary and $p$-tail are stated for functionals with values in $[-\infty,\infty)$ (footnote 2), such as inf-convolutions.
--   5. **The truncation of Theorem 2.** Given $\varepsilon,\alpha$, a random variable $X$ and a quantile uniform $U$ of $X$,
--   $$X^{[\alpha]}=X\,\mathbb 1_{\{U\le 1-\alpha\}}+\mathrm{VaR}^R_{\alpha+\varepsilon}(X)\,\mathbb 1_{\{U>1-\alpha\}}.$$
--
--   These are the properties in which the paper's risk-sharing results are stated.
--
--   **Formalization Note** Risk measures are functions on all of $\Omega\to\mathbb R$, and each property is required only for arguments in the domain $\mathcal X$, which is a parameter. Equality in law of tails is encoded through (6) multiplied by $p$, so no uniform random variable has to be chosen; Definition 1 takes $p\in(0,1)$, and every statement built on it carries that range (the paper's extension to $p=1$, p. 17, is law invariance). Extended-real functionals take values in `EReal`; translation invariance there reads $F(X-m)=F(X)-m$, which is consistent at $\pm\infty$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 5–8, §2.1, §2.2, §2.4, (6), Definition 1, footnote 2; p. 13, Theorem 2 (definition of X^[α])

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

namespace TailRiskSharing.VaRTail

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.1 p. 5: `U` is a uniform random variable on `[0, 1]` with `F⁻¹_X(U) = X` a.s.
Here `F⁻¹_X(p) = TailRiskSharing.VaRConv.VaRL P (1 - p) X`. -/
def IsQuantileUniform (P : Measure Ω) (X U : Ω → ℝ) : Prop :=
  Measurable U ∧ P.map U = volume.restrict (Set.Icc (0:ℝ) 1) ∧
    ∀ᵐ ω ∂P, TailRiskSharing.VaRConv.VaRL P (1 - U ω) X = X ω

/-- §2.4 p. 8, display (6): `X_p =d Y_p`, i.e. `(F_X(x) - (1 - p))_+ = (F_Y(x) - (1 - p))_+`
for every `x`. -/
def TailEquiv (P : Measure Ω) (p : ℝ) (X Y : Ω → ℝ) : Prop :=
  ∀ x : ℝ, max (TailRiskSharing.VaRConv.distFn P X x - (1 - p)) 0 = max (TailRiskSharing.VaRConv.distFn P Y x - (1 - p)) 0

/-- §2.2 p. 5: monotone, `ρ(X) ≤ ρ(Y)` whenever `X ≤ Y` a.s. -/
def IsMonotone (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ᵐ ω ∂P, X ω ≤ Y ω) → ρ X ≤ ρ Y

/-- §2.2 p. 5: translation-invariant, `ρ(X - m) = ρ(X) - m`. -/
def IsTranslationInvariant (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ m : ℝ, ρ (fun ω => X ω - m) = ρ X - m

/-- §2.2 p. 5: monetary = monotone and translation-invariant. -/
def IsMonetary (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  IsMonotone P dom ρ ∧ IsTranslationInvariant dom ρ

/-- §2.2 p. 5: law-invariant. -/
def IsLawInvariant (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ x, TailRiskSharing.VaRConv.distFn P X x = TailRiskSharing.VaRConv.distFn P Y x) → ρ X = ρ Y

/-- Definition 1, p. 8, through (6): `ρ` is a `p`-tail risk measure. -/
def IsTailRiskMeasure (P : Measure Ω) (dom : Set (Ω → ℝ)) (p : ℝ) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, TailEquiv P p X Y → ρ X = ρ Y

/-- §2.2 p. 5 (range `[-∞, ∞)`, footnote 2): monotone, for an `EReal`-valued functional. -/
def IsMonotoneE (P : Measure Ω) (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ᵐ ω ∂P, X ω ≤ Y ω) → F X ≤ F Y

/-- §2.2 p. 5: translation-invariant, for an `EReal`-valued functional. -/
def IsTranslationInvariantE (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) : Prop :=
  ∀ X ∈ dom, ∀ m : ℝ, F (fun ω => X ω - m) = F X - (m : EReal)

/-- §2.2 p. 5: monetary, for an `EReal`-valued functional. -/
def IsMonetaryE (P : Measure Ω) (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) : Prop :=
  IsMonotoneE P dom F ∧ IsTranslationInvariantE dom F

/-- Definition 1, p. 8, through (6), for an `EReal`-valued functional. -/
def IsTailRiskMeasureE (P : Measure Ω) (dom : Set (Ω → ℝ)) (p : ℝ) (F : (Ω → ℝ) → EReal) :
    Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, TailEquiv P p X Y → F X = F Y

/-- Theorem 2, p. 13: `X^[α] = X 1{U ≤ 1-α} + VaR^R_{α+ε}(X) 1{U > 1-α}`. -/
noncomputable def cutAt (P : Measure Ω) (ε α : ℝ) (X U : Ω → ℝ) : Ω → ℝ :=
  fun ω => if U ω ≤ 1 - α then X ω else TailRiskSharing.VaRConv.VaRR P (α + ε) X

end TailRiskSharing.VaRTail


