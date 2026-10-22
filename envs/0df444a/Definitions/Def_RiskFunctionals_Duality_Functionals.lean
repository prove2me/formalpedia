-- Prove2me | Definitions.Def_RiskFunctionals_Duality_Functionals
-- name    : RiskFunctionals_Duality_Functionals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:23.54335+00:00
-- url     : https://prove2.me/theorems/76f37286-9ff4-403b-ae7a-11eb3d19f6b4
-- title:
--   Acceptability functionals (A1)–(A5), deviation risk functionals (D1)–(D3), acceptance sets and non-atomic probability spaces
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\mathcal Y = L_p(\Omega,\mathcal F,P)$, $1\le p\le\infty$, the space of $p$-integrable random variables (almost surely equal variables identified). Functionals are maps $\mathcal A:\mathcal Y\to\overline{\mathbb R}=[-\infty,+\infty]$; a constant $c$ is identified with the constant random variable $c$.
--
--   1. A measurable set $A$ is an **atom** of $P$ if $P(A)>0$ and every measurable $A'\subseteq A$ has $P(A')=P(A)$ or $P(A')=0$. The space is **non-atomic** if $P$ has no atoms.
--   2. The **expectation** is $\mathbb E(Y)=\int_\Omega Y\,dP$.
--   3. Properties of a functional $\mathcal A$ (for all $Y,Y^{(1)},Y^{(2)}\in\mathcal Y$):
--      - (A1) translation equivariance: $\mathcal A(Y+c)=\mathcal A(Y)+c$ for all $c\in\mathbb R$;
--      - (A2) concavity: $\mathcal A(\lambda Y^{(1)}+(1-\lambda)Y^{(2)})\ge\lambda\mathcal A(Y^{(1)})+(1-\lambda)\mathcal A(Y^{(2)})$ for $0\le\lambda\le1$;
--      - (A3) pointwise monotonicity: $Y^{(1)}\le Y^{(2)}$ a.s. implies $\mathcal A(Y^{(1)})\le\mathcal A(Y^{(2)})$;
--      - (A4) positive homogeneity: $\mathcal A(\lambda Y)=\lambda\mathcal A(Y)$ for $\lambda\ge0$;
--      - (A5) strictness: $\mathcal A(Y)\le\mathbb E(Y)$.
--
--      $\mathcal A$ is an **acceptability functional** if it satisfies (A1)–(A3).
--   4. Properties of a functional $\mathcal D$: (D1) translation invariance $\mathcal D(Y+c)=\mathcal D(Y)$; (D2) convexity $\mathcal D(\lambda Y^{(1)}+(1-\lambda)Y^{(2)})\le\lambda\mathcal D(Y^{(1)})+(1-\lambda)\mathcal D(Y^{(2)})$, $0\le\lambda\le1$; (D3) $X\le Y$ a.s. implies $\mathbb E(X)-\mathcal D(X)\le\mathbb E(Y)-\mathcal D(Y)$. $\mathcal D$ is a **deviation risk functional** if it satisfies (D1)–(D3); (D4) is the same formula as (A4).
--   5. $\mathcal A$ is **version-independent** if $Y^{(1)}$ and $Y^{(2)}$ having the same distribution implies $\mathcal A(Y^{(1)})=\mathcal A(Y^{(2)})$.
--   6. For laws $G_1,G_2$ on $\mathbb R$, **first-order stochastic dominance** $G_1\prec_{FSD}G_2$ means $\int U\,dG_1\le\int U\,dG_2$ for every nondecreasing $U$ for which both integrals exist.
--   7. The **acceptance set** of $\mathcal A$ is
--   $$\mathcal S_{\mathcal A}=\{Y\in\mathcal Y:\mathcal A(Y)\ge0\},\tag{2.4}$$
--   and the functional of a set $\mathcal S\subseteq\mathcal Y$ is
--   $$\mathcal A_{\mathcal S}(Y)=\sup\{a\in\mathbb R: Y-a\in\mathcal S\}.\tag{2.5}$$
--   A set $\mathcal S$ is **monotone** if $Y^{(1)}\in\mathcal S$ and $Y^{(1)}\le Y^{(2)}$ a.s. imply $Y^{(2)}\in\mathcal S$, and a **cone** if $Y\in\mathcal S$ implies $\lambda Y\in\mathcal S$ for $\lambda\ge0$.
--
--   These are the objects of §2.2 of the book: the axioms by which acceptability and deviation risk functionals are recognized, and the acceptance sets through which a translation-equivariant functional can be described.
--
--   **Formalization Note** Functionals are `EReal`-valued, as the book's probability functionals are extended real valued (p. 27). (A2), (D2) and (A4) are computed in `EReal`, where $0\cdot(\pm\infty)=0$ and $(+\infty)+(-\infty)=-\infty$; for the functionals the book considers (never taking both $+\infty$ and $-\infty$) this is the book's inequality. The supremum in (2.5) is taken in $[-\infty,+\infty]$: it is $-\infty$ if no $a$ qualifies and $+\infty$ if the qualifying $a$ are unbounded. Non-atomicity is the book's atom definition (p. 265), which is stronger than Mathlib's `NoAtoms` (null singletons). The order $\prec_{FSD}$ duplicates Definition 1.10(i) of chapter 1, which is a separate draft.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 35–38, Definitions 2.17, 2.19–2.21, 2.23; p. 28, Definition 2.1; p. 13, Definition 1.10(i); p. 40, Eqs. (2.4)–(2.5) and Proposition 2.26(iii)–(iv); p. 265, Appendix A (atoms)

import Mathlib

namespace RiskFunctionals.Duality

open MeasureTheory ProbabilityTheory

/-- An atom of `P` (Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific
2007, p. 265, Appendix A): a measurable set `A` with `P(A) > 0` such that every measurable
`A' ⊆ A` has `P(A') = P(A)` or `P(A') = 0`. -/
def IsAtomOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ 0 < P A ∧ ∀ A' ⊆ A, MeasurableSet A' → P A' = P A ∨ P A' = 0

/-- A non-atomic probability space (p. 265: "A probability space is called non-atomic if `P` has
no atoms"); the book assumes it throughout (p. 4). This is stronger than Mathlib's `NoAtoms`,
which only asks singletons to be null. -/
def IsNonAtomic {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Prop :=
  ∀ A : Set Ω, ¬ IsAtomOf P A

/-- The expectation `𝔼(Y) = ∫ Y dP` of an element of `L_p(Ω, ℱ, P)`. -/
noncomputable def expectation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (Y : Lp ℝ p P) : ℝ :=
  ∫ ω, Y ω ∂P

/-- (A1) Translation equivariance (p. 36, Definition 2.17; p. 29, Definition 2.2(i)):
`𝒜(Y + c) = 𝒜(Y) + c` for all constants `c`. Functionals take values in `EReal` (p. 27: a
probability functional is extended real valued). -/
def TranslationEquivariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {p : ENNReal} (A : Lp ℝ p P → EReal) : Prop :=
  ∀ (Y : Lp ℝ p P) (c : ℝ), A (Y + Lp.const p P c) = A Y + (c : EReal)

/-- (A2) Concavity (p. 36, Definition 2.17; p. 30, Definition 2.6(ii)):
`𝒜(λY⁽¹⁾ + (1 − λ)Y⁽²⁾) ≥ λ𝒜(Y⁽¹⁾) + (1 − λ)𝒜(Y⁽²⁾)` for `0 ≤ λ ≤ 1`, computed in `EReal`
(where `0 · (−∞) = 0` and `(+∞) + (−∞) = −∞`). -/
def ConcaveFunctional {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (A : Lp ℝ p P → EReal) : Prop :=
  ∀ (Y₁ Y₂ : Lp ℝ p P) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    (lam : EReal) * A Y₁ + ((1 - lam : ℝ) : EReal) * A Y₂ ≤ A (lam • Y₁ + (1 - lam) • Y₂)

/-- (A3) Pointwise monotonicity (p. 36, Definition 2.17; p. 29, Definition 2.4):
`Y⁽¹⁾ ≤ Y⁽²⁾` a.s. implies `𝒜(Y⁽¹⁾) ≤ 𝒜(Y⁽²⁾)`. -/
def PointwiseMonotone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ENNReal}
    (A : Lp ℝ p P → EReal) : Prop :=
  ∀ Y₁ Y₂ : Lp ℝ p P, (∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) → A Y₁ ≤ A Y₂

/-- (A4) Positive homogeneity (p. 36, Definition 2.19): `𝒜(λY) = λ𝒜(Y)` for `λ ≥ 0`. The same
formula is (D4) for a deviation risk functional (p. 38, Definition 2.23). -/
def PositivelyHomogeneous {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (A : Lp ℝ p P → EReal) : Prop :=
  ∀ (Y : Lp ℝ p P) (lam : ℝ), 0 ≤ lam → A (lam • Y) = (lam : EReal) * A Y

/-- (A5) Strictness (p. 36, Definition 2.20): `𝒜(Y) ≤ 𝔼(Y)`. -/
def Strict {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (A : Lp ℝ p P → EReal) : Prop :=
  ∀ Y : Lp ℝ p P, A Y ≤ (expectation Y : EReal)

/-- An acceptability functional (p. 35–36, Definition 2.17): a functional on `L_p` satisfying
(A1) translation equivariance, (A2) concavity and (A3) pointwise monotonicity. -/
structure IsAcceptabilityFunctional {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {p : ENNReal} (A : Lp ℝ p P → EReal) : Prop where
  translationEquivariant : TranslationEquivariant P A
  concave : ConcaveFunctional A
  monotone : PointwiseMonotone P A

/-- (D1) Translation invariance (p. 37, Definition 2.21; p. 29, Definition 2.2(ii)):
`𝒟(Y + c) = 𝒟(Y)` for constants `c`. -/
def TranslationInvariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {p : ENNReal} (D : Lp ℝ p P → EReal) : Prop :=
  ∀ (Y : Lp ℝ p P) (c : ℝ), D (Y + Lp.const p P c) = D Y

/-- (D2) Convexity (p. 37, Definition 2.21; p. 30, Definition 2.6(i)):
`𝒟(λY⁽¹⁾ + (1 − λ)Y⁽²⁾) ≤ λ𝒟(Y⁽¹⁾) + (1 − λ)𝒟(Y⁽²⁾)` for `0 ≤ λ ≤ 1`, computed in `EReal`. -/
def ConvexFunctional {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (D : Lp ℝ p P → EReal) : Prop :=
  ∀ (Y₁ Y₂ : Lp ℝ p P) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    D (lam • Y₁ + (1 - lam) • Y₂) ≤ (lam : EReal) * D Y₁ + ((1 - lam : ℝ) : EReal) * D Y₂

/-- (D3) Monotonicity of `𝔼 − 𝒟` (p. 37, Definition 2.21): `X ≤ Y` (a.s.) implies
`𝔼(X) − 𝒟(X) ≤ 𝔼(Y) − 𝒟(Y)`. -/
def MeanMinusMonotone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ENNReal}
    (D : Lp ℝ p P → EReal) : Prop :=
  ∀ X Y : Lp ℝ p P, (∀ᵐ ω ∂P, X ω ≤ Y ω) →
    (expectation X : EReal) - D X ≤ (expectation Y : EReal) - D Y

/-- A deviation risk functional (p. 37, Definition 2.21): a functional on `L_p` satisfying
(D1) translation invariance, (D2) convexity and (D3) monotonicity of `𝔼 − 𝒟`. -/
structure IsDeviationRiskFunctional {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {p : ENNReal} (D : Lp ℝ p P → EReal) : Prop where
  translationInvariant : TranslationInvariant P D
  convex : ConvexFunctional D
  monotone : MeanMinusMonotone P D

/-- Version independence (p. 28, Definition 2.1): equal laws give equal values. -/
def VersionIndependent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ENNReal}
    (A : Lp ℝ p P → EReal) : Prop :=
  ∀ Y₁ Y₂ : Lp ℝ p P, IdentDistrib Y₁ Y₂ P P → A Y₁ = A Y₂

/-- First-order stochastic dominance `G₁ ≺_FSD G₂` (p. 13, Definition 1.10(i)) for laws `μ₁`,
`μ₂` on `ℝ`: `∫ U dG₁ ≤ ∫ U dG₂` for every nondecreasing `U` for which both integrals exist. -/
def FSD (μ₁ μ₂ : Measure ℝ) : Prop :=
  ∀ U : ℝ → ℝ, Monotone U → Integrable U μ₁ → Integrable U μ₂ →
    ∫ v, U v ∂μ₁ ≤ ∫ v, U v ∂μ₂

/-- The acceptance set `𝒮_𝒜 = {Y : 𝒜(Y) ≥ 0}` (p. 40, Eq. (2.4)). -/
def acceptanceSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (A : Lp ℝ p P → EReal) : Set (Lp ℝ p P) :=
  {Y | 0 ≤ A Y}

/-- The functional of an acceptance set, `𝒜_𝒮(Y) := sup{a : Y − a ∈ 𝒮}` (p. 40, Eq. (2.5)),
as a supremum in `EReal`: it is `−∞` when no `a` qualifies and `+∞` when the qualifying `a` are
unbounded above. -/
noncomputable def acceptabilityOfSet {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {p : ENNReal} (S : Set (Lp ℝ p P)) (Y : Lp ℝ p P) : EReal :=
  sSup ((fun a : ℝ => (a : EReal)) '' {a : ℝ | Y - Lp.const p P a ∈ S})

/-- A monotone set (p. 40, Proposition 2.26(iii)): `Y⁽¹⁾ ∈ 𝒮` and `Y⁽¹⁾ ≤ Y⁽²⁾` (a.s.) imply
`Y⁽²⁾ ∈ 𝒮`. -/
def MonotoneSet {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ENNReal}
    (S : Set (Lp ℝ p P)) : Prop :=
  ∀ Y₁ Y₂ : Lp ℝ p P, Y₁ ∈ S → (∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) → Y₂ ∈ S

/-- A cone (p. 40, Proposition 2.26(iv)): `Y ∈ 𝒮` implies `λY ∈ 𝒮` for `λ ≥ 0`. -/
def IsConeSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (S : Set (Lp ℝ p P)) : Prop :=
  ∀ Y ∈ S, ∀ lam : ℝ, 0 ≤ lam → lam • Y ∈ S

end RiskFunctionals.Duality


