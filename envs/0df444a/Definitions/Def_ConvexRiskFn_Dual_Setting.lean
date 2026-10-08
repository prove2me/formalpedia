-- Prove2me | Definitions.Def_ConvexRiskFn_Dual_Setting
-- name    : ConvexRiskFn_Dual_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:17.891986+00:00
-- url     : https://prove2.me/theorems/fa614743-fb1a-42c8-a9a4-e47a808ae8c3
-- title:
--   §1–§2, pp. 433–435 — paired spaces of functions and signed measures, condition (C), axioms (A1)–(A4), conjugate, biconjugate, dual domain, lsc hull
-- statement:
--   This file fixes the framework of §2 of Ruszczyński and Shapiro, *Optimization of convex risk functions*, in which outcomes are costs: the smaller the value of $X$, the better.
--
--   **Spaces.** Let $(\Omega,\mathcal F)$ be a measurable space and $\mathbb Y$ the linear space of all finite signed measures on it; for $\mu\in\mathbb Y$ with Jordan decomposition $\mu=\mu^+-\mu^-$, $|\mu|=\mu^++\mu^-$ is its total variation measure. A **paired system** consists of
--
--   1. a real locally convex topological vector space $\mathcal X$ whose elements are $\mathcal F$-measurable functions $X:\Omega\to\mathbb R$ (the vector operations are the pointwise ones; $\mathcal X$ keeps its own topology, for instance a norm);
--   2. a linear subspace $\mathcal Y\subseteq\mathbb Y$ such that $\int_\Omega |X|\,d|\mu|<+\infty$ for all $X\in\mathcal X$, $\mu\in\mathcal Y$;
--   3. the scalar product
--   $$\langle \mu, X\rangle := \int_\Omega X(\omega)\,d\mu(\omega)=\int_\Omega X\,d\mu^+-\int_\Omega X\,d\mu^- ,\qquad (2.2)$$
--   with which the topology of $\mathcal X$ is compatible: each $\langle\mu,\cdot\rangle$, $\mu\in\mathcal Y$, is continuous on $\mathcal X$, and every continuous linear functional on $\mathcal X$ equals $\langle\mu,\cdot\rangle$ for some $\mu\in\mathcal Y$.
--
--   **Cones and order.** $\mathcal X_+=\{X\in\mathcal X: X(\omega)\ge 0\ \forall\omega\}$ (2.1); $Y\succeq X$ means $Y(\omega)\ge X(\omega)$ for all $\omega$. $\mathcal Y_+$ is the set of nonnegative measures in $\mathcal Y$ and $\mathcal P=\{\mu\in\mathcal Y_+:\mu(\Omega)=1\}$ the probability measures in $\mathcal Y$.
--
--   **Condition (C).** If $\mu\in\mathcal Y\setminus\mathcal Y_+$, then $\langle\mu,X\rangle<0$ for some $X\in\mathcal X_+$.
--
--   **Risk functions.** A risk function is $\rho:\mathcal X\to\overline{\mathbb R}=\mathbb R\cup\{\pm\infty\}$. It is **proper** if $\rho(X)>-\infty$ for every $X$ and $\operatorname{dom}\rho=\{X:\rho(X)<+\infty\}$ is nonempty. The axioms are
--
--   - (A1) Convexity: $\rho(\alpha X+(1-\alpha)Y)\le\alpha\rho(X)+(1-\alpha)\rho(Y)$ for all $X,Y\in\mathcal X$, $\alpha\in[0,1]$;
--   - (A2) Monotonicity: $Y\succeq X$ implies $\rho(Y)\ge\rho(X)$;
--   - (A3) Translation equivariance: $\rho(X+a)=\rho(X)+a$ for $a\in\mathbb R$, $X\in\mathcal X$;
--   - (A4) Positive homogeneity: $\rho(tX)=t\rho(X)$ for $t>0$, $X\in\mathcal X$.
--
--   **Duality.** The conjugate and biconjugate are
--   $$\rho^*(\mu)=\sup_{X\in\mathcal X}\{\langle\mu,X\rangle-\rho(X)\}\ (2.3),\qquad \rho^{**}(X)=\sup_{\mu\in\mathcal Y}\{\langle\mu,X\rangle-\rho^*(\mu)\}\ (2.4),$$
--   the dual domain is $\mathcal A=\operatorname{dom}\rho^*=\{\mu\in\mathcal Y:\rho^*(\mu)<+\infty\}$, and $\operatorname{lsc}(\rho)(X)=\liminf_{Z\to X}\rho(Z)$ is the lower semicontinuous hull of $\rho$ in the topology of $\mathcal X$.
--
--   These objects are shared by every statement of the mission: the dual representation theorem and the characterizations of (A2)–(A4) are all phrased in terms of $\rho^*$ and $\mathcal A$.
--
--   **Formalization Note** $\mathcal X$ is an abstract real vector space with its own topology and an injective linear map into $\Omega\to\mathbb R$, so that it is not forced to carry the topology of pointwise convergence. Values are in `EReal`, where $r-(+\infty)=-\infty$; suprema are `iSup` in the complete lattice `EReal`. In (A1) the product $0\cdot(+\infty)$ is $0$. In (A3) the constant function $a$ is written $a\cdot\mathbf 1$ for an element $\mathbf 1\in\mathcal X$ that a theorem requires to be the constant function $1$. The topology of $\mathcal Y$ is not modelled: no statement of the mission uses it. Condition (C) is a separate predicate, assumed by the statements that use it.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 433 (axioms (A1)–(A4)), p. 434 (§2, (2.1), (2.2), condition (C)), pp. 434–435 (paired locally convex spaces), p. 435 (proper, (2.3), (2.4), lsc(ρ), 𝒜 := dom(ρ*))

import Mathlib

namespace ConvexRiskFn.Dual

open MeasureTheory Filter Topology

/-- The scalar product (2.2) of Ruszczyński–Shapiro: `⟨μ, X⟩ = ∫_Ω X dμ`, for a finite signed
measure `μ`, computed through the Jordan decomposition `μ = μ⁺ − μ⁻` as
`∫ X dμ⁺ − ∫ X dμ⁻`. -/
noncomputable def pair {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω) (X : Ω → ℝ) : ℝ :=
  (∫ ω, X ω ∂μ.toJordanDecomposition.posPart) - ∫ ω, X ω ∂μ.toJordanDecomposition.negPart

/-- The framework of §2 (pp. 434–435). `𝒳` is a linear space of `ℱ`-measurable functions
`X : Ω → ℝ`, carried as an abstract real vector space with its own topology together with an
injective linear map `toFun` into `Ω → ℝ`; `Y` is a linear space `𝒴 ⊆ 𝕐` of finite signed
measures on `(Ω, ℱ)` such that `∫ |X| d|μ| < ∞` for every `X ∈ 𝒳` and `μ ∈ 𝒴`; and the topology
of `𝒳` is compatible with the scalar product (2.2): every functional `⟨μ, ·⟩`, `μ ∈ 𝒴`, is
continuous on `𝒳`, and every continuous linear functional on `𝒳` is of the form `⟨μ, ·⟩` for some
`μ ∈ 𝒴`. -/
structure PairedSpaces (Ω : Type*) [MeasurableSpace Ω] (𝒳 : Type*) [AddCommGroup 𝒳]
    [Module ℝ 𝒳] [TopologicalSpace 𝒳] where
  /-- The realisation of an element of `𝒳` as a function `Ω → ℝ`. -/
  toFun : 𝒳 →ₗ[ℝ] (Ω → ℝ)
  injective : Function.Injective toFun
  /-- Every element of `𝒳` is an `ℱ`-measurable function. -/
  measurable : ∀ X, Measurable (toFun X)
  /-- The linear space `𝒴 ⊆ 𝕐` of finite signed measures paired with `𝒳`. -/
  Y : Submodule ℝ (SignedMeasure Ω)
  /-- `∫_Ω |X| d|μ| < +∞` for every `X ∈ 𝒳` and `μ ∈ 𝒴`. -/
  integrable : ∀ μ ∈ Y, ∀ X, Integrable (toFun X) μ.totalVariation
  /-- Compatibility: each `⟨μ, ·⟩`, `μ ∈ 𝒴`, is a continuous functional on `𝒳`. -/
  continuous_pair : ∀ μ ∈ Y, Continuous fun X => pair μ (toFun X)
  /-- Compatibility: every continuous linear functional on `𝒳` is `⟨μ, ·⟩` for some `μ ∈ 𝒴`. -/
  dual_rep : ∀ ℓ : 𝒳 →L[ℝ] ℝ, ∃ μ ∈ Y, ∀ X, ℓ X = pair μ (toFun X)

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
  [TopologicalSpace 𝒳]

/-- The cone `𝒳₊ = {X ∈ 𝒳 : X(ω) ≥ 0 ∀ ω ∈ Ω}` of (2.1). -/
def Xpos (S : PairedSpaces Ω 𝒳) : Set 𝒳 := {X | ∀ ω, 0 ≤ S.toFun X ω}

/-- `𝒴₊`, the nonnegative measures in `𝒴`. -/
def Ypos (S : PairedSpaces Ω 𝒳) : Set (SignedMeasure Ω) := {μ | μ ∈ S.Y ∧ 0 ≤ μ}

/-- `𝒫`, the probability measures in `𝒴`: `μ ∈ 𝒴₊` and `μ(Ω) = 1`. -/
def Prob (S : PairedSpaces Ω 𝒳) : Set (SignedMeasure Ω) :=
  {μ | μ ∈ S.Y ∧ 0 ≤ μ ∧ μ Set.univ = 1}

/-- Condition (C), p. 434: if `μ ∈ 𝒴` is not nonnegative, then `⟨μ, X⟩ < 0` for some `X ∈ 𝒳₊`. -/
def CondC (S : PairedSpaces Ω 𝒳) : Prop :=
  ∀ μ ∈ S.Y, ¬ (0 ≤ μ) → ∃ X ∈ Xpos S, pair μ (S.toFun X) < 0

/-- A risk function `ρ : 𝒳 → ℝ̄` is proper (p. 435): `ρ(X) > −∞` for all `X` and
`dom ρ = {X : ρ(X) < +∞}` is nonempty. -/
def IsProper (ρ : 𝒳 → EReal) : Prop := (∀ X, ⊥ < ρ X) ∧ ∃ X, ρ X < ⊤

/-- The domain `dom ρ = {X ∈ 𝒳 : ρ(X) < +∞}`. -/
def dom (ρ : 𝒳 → EReal) : Set 𝒳 := {X | ρ X < ⊤}

/-- (A1) Convexity: `ρ(αX + (1 − α)Y) ≤ αρ(X) + (1 − α)ρ(Y)` for all `X, Y` and `α ∈ [0, 1]`. -/
def A1 (ρ : 𝒳 → EReal) : Prop :=
  ∀ X Y : 𝒳, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    ρ (α • X + (1 - α) • Y) ≤ ((α : ℝ) : EReal) * ρ X + ((1 - α : ℝ) : EReal) * ρ Y

/-- (A2) Monotonicity: if `Y ⪰ X` (i.e. `Y(ω) ≥ X(ω)` for all `ω`), then `ρ(Y) ≥ ρ(X)`. -/
def A2 (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) : Prop :=
  ∀ X Y : 𝒳, (∀ ω, S.toFun X ω ≤ S.toFun Y ω) → ρ X ≤ ρ Y

/-- (A3) Translation equivariance: `ρ(X + a) = ρ(X) + a` for `a ∈ ℝ`; the constant function `a`
is `a • one`, where `one ∈ 𝒳` is the constant function `1`. -/
def A3 (one : 𝒳) (ρ : 𝒳 → EReal) : Prop :=
  ∀ (a : ℝ) (X : 𝒳), ρ (X + a • one) = ρ X + ((a : ℝ) : EReal)

/-- (A4) Positive homogeneity: `ρ(tX) = tρ(X)` for `t > 0`. -/
def A4 (ρ : 𝒳 → EReal) : Prop :=
  ∀ (t : ℝ) (X : 𝒳), 0 < t → ρ (t • X) = ((t : ℝ) : EReal) * ρ X

/-- The conjugate (2.3): `ρ*(μ) = sup_{X ∈ 𝒳} {⟨μ, X⟩ − ρ(X)}`. -/
noncomputable def conj (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) (μ : SignedMeasure Ω) : EReal :=
  ⨆ X : 𝒳, ((pair μ (S.toFun X) : ℝ) : EReal) - ρ X

/-- The biconjugate (2.4): `ρ**(X) = sup_{μ ∈ 𝒴} {⟨μ, X⟩ − ρ*(μ)}`. -/
noncomputable def biconj (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) (X : 𝒳) : EReal :=
  ⨆ μ : S.Y, ((pair (μ : SignedMeasure Ω) (S.toFun X) : ℝ) : EReal) - conj S ρ μ

/-- `𝒜 = dom(ρ*) = {μ ∈ 𝒴 : ρ*(μ) < +∞}`. -/
def dualDom (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) : Set (SignedMeasure Ω) :=
  {μ | μ ∈ S.Y ∧ conj S ρ μ < ⊤}

/-- The lower semicontinuous hull `lsc(ρ)` in the topology of `𝒳`:
`lsc(ρ)(X) = liminf_{Z → X} ρ(Z)`, the largest lower semicontinuous minorant of `ρ`. -/
noncomputable def lscHull (ρ : 𝒳 → EReal) (X : 𝒳) : EReal :=
  Filter.liminf ρ (𝓝 X)

end ConvexRiskFn.Dual


