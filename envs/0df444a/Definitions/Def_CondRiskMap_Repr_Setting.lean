-- Prove2me | Definitions.Def_CondRiskMap_Repr_Setting
-- name    : CondRiskMap_Repr_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:18.861699+00:00
-- url     : https://prove2.me/theorems/46c1f11e-29bd-411a-83e8-ef0f95b7e394
-- title:
--   §2–§4, pp. 2–10 — paired spaces with ℱ₁ ⊂ ℱ₂, (C), (C′), conditional risk mappings, conjugate (3.4), 𝒫_{𝒴₂|ℱ₁}(ω), 𝒜(ω), weak* measurability, ℚ_μ, (K), conditional probability
-- statement:
--   This file fixes the setting of Ruszczyński and Shapiro's *Conditional risk mappings* (§2–§4).
--
--   **Spaces.** Let $\Omega$ be a set with two $\sigma$-algebras $\mathcal F_1\subset\mathcal F_2$. The space $\mathcal X_2$ is a real vector space of $\mathcal F_2$-measurable functions $X:\Omega\to\mathbb R$, and $\mathcal X_1\subset\mathcal X_2$ is a linear subspace of $\mathcal F_1$-measurable functions. The space $\mathcal Y_2$ is a real vector space of finite signed measures on $(\Omega,\mathcal F_2)$ such that $\int_\Omega|X|\,d|\mu|<\infty$ for all $X\in\mathcal X_2$, $\mu\in\mathcal Y_2$. The scalar product is
--   $$
--   \langle\mu,X\rangle=\int_\Omega X(\omega)\,d\mu(\omega)\qquad(2.2).
--   $$
--   $\mathcal X_2$ and $\mathcal Y_2$ carry their own topologies and are **paired**: every functional $\langle\mu,\cdot\rangle$ is continuous on $\mathcal X_2$ and every $\langle\cdot,X\rangle$ is continuous on $\mathcal Y_2$; every continuous linear functional on $\mathcal X_2$ is $\langle\mu,\cdot\rangle$ for some $\mu\in\mathcal Y_2$, and every continuous linear functional on $\mathcal Y_2$ is $\langle\cdot,X\rangle$ for some $X\in\mathcal X_2$.
--
--   **Standing conditions.**
--   1. (C): if $\mu\in\mathcal Y_2$ is not nonnegative, there is $X\in\mathcal X_2$ with $X(\omega)\ge0$ for all $\omega$ and $\langle\mu,X\rangle<0$.
--   2. (C′): for every $B\in\mathcal F_1$ the indicator $\mathbb 1_B$ belongs to $\mathcal X_1$.
--   3. *Indicators in $\mathcal X_2$*: for every $A\in\mathcal F_2$ the indicator $\mathbb 1_A$ belongs to $\mathcal X_2$ (the paper's example of a space satisfying (C), p. 4).
--
--   **Probability measures.** $\mathcal P_{\mathcal Y_2}$ is the set of $\mu\in\mathcal Y_2$ that are nonnegative with $\mu(\Omega)=1$. For $\omega\in\Omega$, $\mathcal P_{\mathcal Y_2|\mathcal F_1}(\omega)$ is the set of $\nu\in\mathcal P_{\mathcal Y_2}$ with $\nu(B)=1$ if $\omega\in B$ and $\nu(B)=0$ if $\omega\notin B$, for every $B\in\mathcal F_1$ (3.5).
--
--   **Conditional risk mappings** (Definition 1). A map $\rho:\mathcal X_2\to\mathcal X_1$, with $\rho_\omega(X)=[\rho(X)](\omega)$ (2.1), is a conditional risk mapping if, for every $\omega\in\Omega$:
--   1. (A1) $\rho_\omega(tX+(1-t)Y)\le t\rho_\omega(X)+(1-t)\rho_\omega(Y)$ for $t\in[0,1]$ and $X,Y\in\mathcal X_2$;
--   2. (A2) if $Y(\omega')\ge X(\omega')$ for every $\omega'\in\Omega$, then $\rho_\omega(Y)\ge\rho_\omega(X)$;
--   3. (A3) $\rho(X+Y)=\rho(X)+Y$ for $Y\in\mathcal X_1$, $X\in\mathcal X_2$.
--
--   It is **positively homogeneous** if $\rho(tX)=t\rho(X)$ for all $X$ and $t>0$ (2.3), and **lower semicontinuous** if every $\rho_\omega:\mathcal X_2\to\mathbb R$ is lower semicontinuous.
--
--   **Conjugate and risk envelope.** The conjugate is the extended-real function
--   $$
--   \rho^*(\mu,\omega)=\sup_{X\in\mathcal X_2}\{\langle\mu,X\rangle-\rho_\omega(X)\}\qquad(3.4),
--   $$
--   and $\mathcal A(\omega)=\{\mu\in\mathcal Y_2:\rho^*(\mu,\omega)<+\infty\}$ is its domain.
--
--   **Selections and the operator $\mathbb Q_\mu$.** A map $\omega\mapsto\mu_\omega\in\mathcal Y_2$ is **weakly\* $\mathcal F_1$-measurable** if $\omega\mapsto\langle\mu_\omega,X\rangle$ is $\mathcal F_1$-measurable for each $X\in\mathcal X_2$ (Definition 2); a selection of $\mathcal A$ moreover has $\mu_\omega\in\mathcal A(\omega)$ for all $\omega$. For such $\mu$, $[\mathbb Q_\mu(\nu)](A)=\int_\Omega\mu_\omega(A)\,d\nu(\omega)$ (4.4), and $\nu$ is a **fixed point** if $\int_\Omega\mu_\omega(A)\,d\nu(\omega)=\nu(A)$ for every $A\in\mathcal F_2$ (4.5).
--
--   **Assumption (K)** (p. 10): $\mathcal P_{\mathcal Y_2}$ is compact and, for every weakly\* $\mathcal F_1$-measurable selection $\mu$ of $\mathcal A$, $\mathbb Q_\mu$ maps $\mathcal P_{\mathcal Y_2}$ into itself and has a closed graph there.
--
--   **Conditional probability** (Billingsley, p. 430; (4.6)). $\mu(\cdot)$ is the conditional probability of $\nu$ with respect to $\mathcal F_1$ if, for every $A\in\mathcal F_2$, $\omega\mapsto\mu_\omega(A)$ is $\mathcal F_1$-measurable and $\int_S\mu_\omega(A)\,d\nu(\omega)=\nu(A\cap S)$ for every $S\in\mathcal F_1$. When moreover $\nu$ and every $\mu_\omega$ are probability measures and $\mu$ is weakly\* $\mathcal F_1$-measurable, $\langle\mu_\omega,X\rangle$ is a version of $\mathbb E_\nu[X|\mathcal F_1](\omega)$ defined at every $\omega$.
--
--   These objects carry the paper's conditional duality theory and its representation of positively homogeneous conditional risk mappings as suprema of conditional expectations.
--
--   **Formalization Note** $\mathcal X_2$ and $\mathcal Y_2$ are abstract real vector spaces with their own topologies, realised by injective linear maps into $\Omega\to\mathbb R$ and into Mathlib's `SignedMeasure Ω`; the ambient `MeasurableSpace Ω` is $\mathcal F_2$ and $\mathcal F_1$ is a second one with $\mathcal F_1\le\mathcal F_2$. The pairing is $\int X\,d\mu^+-\int X\,d\mu^-$ through the Jordan decomposition. The space $\mathcal Y_1$ of the paper is not modelled (nothing in this mission uses it). The conjugate takes values in `EReal`. In (K), $\mathbb Q_\mu$ is a map `q` on $\mathcal Y_2$ whose values on $\mathcal P_{\mathcal Y_2}$ are given by (4.4); the graph condition is on $\mathcal P_{\mathcal Y_2}$, the paper's weakest form ("or, more generally, has a closed graph").
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, pp. 2–4 (Definition 1, (2.1)–(2.3), (C), (C′)), pp. 4–5 ((3.4), (3.5)), p. 6 ((3.8), 𝒜(ω)), pp. 8–10 (Definition 2, (4.4), (4.5), (4.6), (K))

import Mathlib

namespace CondRiskMap.Repr

open MeasureTheory

/-- The scalar product (2.2): `⟨μ, X⟩ = ∫_Ω X dμ` for a finite signed measure `μ`, computed
through the Jordan decomposition `μ = μ⁺ − μ⁻` as `∫ X dμ⁺ − ∫ X dμ⁻`. -/
noncomputable def pair {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω) (X : Ω → ℝ) : ℝ :=
  (∫ ω, X ω ∂μ.toJordanDecomposition.posPart) - ∫ ω, X ω ∂μ.toJordanDecomposition.negPart

/-- The setting of §2 (pp. 2–3). The ambient `MeasurableSpace Ω` is `ℱ₂`; `F₁ ≤ ℱ₂` is `ℱ₁`.
`𝒳` (the space `𝒳₂`) and `𝒴` (the space `𝒴₂`) are abstract real vector spaces carrying their own
topologies, realised by injective linear maps `toFun : 𝒳 → (Ω → ℝ)` (into `ℱ₂`-measurable
functions) and `toMeasure : 𝒴 → SignedMeasure Ω` (finite signed measures on `(Ω, ℱ₂)`), with
`∫ |X| d|μ| < ∞` for all `X`, `μ`. `X₁ ⊆ 𝒳` is the subspace `𝒳₁` of `ℱ₁`-measurable elements.
The topologies are compatible with (2.2): each `⟨μ, ·⟩` is continuous on `𝒳` and each `⟨·, X⟩`
is continuous on `𝒴`, every continuous linear functional on `𝒳` is `⟨μ, ·⟩` for some `μ ∈ 𝒴`,
and every continuous linear functional on `𝒴` is `⟨·, X⟩` for some `X ∈ 𝒳`. -/
structure PairedSpaces (Ω : Type*) [m₂ : MeasurableSpace Ω] (𝒳 𝒴 : Type*)
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴] where
  /-- An element of `𝒳₂` as a real function on `Ω`. -/
  toFun : 𝒳 →ₗ[ℝ] (Ω → ℝ)
  toFun_injective : Function.Injective toFun
  /-- Every element of `𝒳₂` is `ℱ₂`-measurable. -/
  measurable : ∀ X, Measurable (toFun X)
  /-- An element of `𝒴₂` as a finite signed measure on `(Ω, ℱ₂)`. -/
  toMeasure : 𝒴 →ₗ[ℝ] SignedMeasure Ω
  toMeasure_injective : Function.Injective toMeasure
  /-- `∫_Ω |X| d|μ| < +∞` for every `X ∈ 𝒳₂` and `μ ∈ 𝒴₂`. -/
  integrable : ∀ μ X, Integrable (toFun X) (toMeasure μ).totalVariation
  /-- Compatibility: `⟨μ, ·⟩` is continuous on `𝒳₂`. -/
  continuous_pair_X : ∀ μ, Continuous fun X => pair (toMeasure μ) (toFun X)
  /-- Compatibility: every continuous linear functional on `𝒳₂` is `⟨μ, ·⟩`. -/
  dual_rep_X : ∀ ℓ : 𝒳 →L[ℝ] ℝ, ∃ μ, ∀ X, ℓ X = pair (toMeasure μ) (toFun X)
  /-- Compatibility: `⟨·, X⟩` is continuous on `𝒴₂`. -/
  continuous_pair_Y : ∀ X, Continuous fun μ => pair (toMeasure μ) (toFun X)
  /-- Compatibility: every continuous linear functional on `𝒴₂` is `⟨·, X⟩`. -/
  dual_rep_Y : ∀ ℓ : 𝒴 →L[ℝ] ℝ, ∃ X, ∀ μ, ℓ μ = pair (toMeasure μ) (toFun X)
  /-- The sub-σ-algebra `ℱ₁ ⊂ ℱ₂`. -/
  F₁ : MeasurableSpace Ω
  F₁_le : F₁ ≤ m₂
  /-- The subspace `𝒳₁ ⊂ 𝒳₂`. -/
  X₁ : Submodule ℝ 𝒳
  /-- Every element of `𝒳₁` is `ℱ₁`-measurable. -/
  X₁_measurable : ∀ Y ∈ X₁, Measurable[F₁] (toFun Y)

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
  [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
  [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]

/-- (2.1): `ρ_ω(X) = [ρ(X)](ω)`. -/
def ρω (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (ω : Ω) (X : 𝒳) : ℝ := S.toFun (ρ X) ω

/-- Condition (C), p. 4: if `μ ∈ 𝒴₂` is not nonnegative, then `⟨μ, X⟩ < 0` for some `X ⪰ 0`. -/
def CondC (S : PairedSpaces Ω 𝒳 𝒴) : Prop :=
  ∀ μ, ¬ (0 ≤ S.toMeasure μ) → ∃ X, (∀ ω, 0 ≤ S.toFun X ω) ∧ pair (S.toMeasure μ) (S.toFun X) < 0

/-- Condition (C′), p. 4: for every `B ∈ ℱ₁`, the indicator `𝟙_B` belongs to `𝒳₁`. -/
def CondC' (S : PairedSpaces Ω 𝒳 𝒴) : Prop :=
  ∀ B, MeasurableSet[S.F₁] B → ∃ Y ∈ S.X₁, S.toFun Y = B.indicator 1

/-- `𝒳₂` contains every indicator `𝟙_A`, `A ∈ ℱ₂` (the example making (C) hold, p. 4). -/
def HasIndicators (S : PairedSpaces Ω 𝒳 𝒴) : Prop :=
  ∀ A, MeasurableSet A → ∃ X, S.toFun X = A.indicator 1

/-- `𝒫_{𝒴₂}`: the probability measures in `𝒴₂` (p. 3). -/
def Prob (S : PairedSpaces Ω 𝒳 𝒴) : Set 𝒴 :=
  {μ | 0 ≤ S.toMeasure μ ∧ S.toMeasure μ Set.univ = 1}

/-- `𝒫_{𝒴₂|ℱ₁}(ω)`, (3.5): the `ν ∈ 𝒫_{𝒴₂}` with `ν(B) = 𝟙_B(ω)` for every `B ∈ ℱ₁`. -/
def ProbGiven (S : PairedSpaces Ω 𝒳 𝒴) (ω : Ω) : Set 𝒴 :=
  {μ | μ ∈ Prob S ∧ ∀ B, MeasurableSet[S.F₁] B → S.toMeasure μ B = B.indicator 1 ω}

/-- `ρ` maps `𝒳₂` into `𝒳₁`. -/
def MapsToX₁ (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) : Prop := ∀ X, ρ X ∈ S.X₁

/-- (A1) Convexity, pointwise in `ω`. -/
def A1 (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ X Y : 𝒳, ∀ ω,
    ρω S ρ ω (t • X + (1 - t) • Y) ≤ t * ρω S ρ ω X + (1 - t) * ρω S ρ ω Y

/-- (A2) Monotonicity: if `Y(ω) ≥ X(ω)` for every `ω`, then `ρ(Y)(ω) ≥ ρ(X)(ω)` for every `ω`. -/
def A2 (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) : Prop :=
  ∀ X Y : 𝒳, (∀ ω, S.toFun X ω ≤ S.toFun Y ω) → ∀ ω, ρω S ρ ω X ≤ ρω S ρ ω Y

/-- (A3) Translation equivariance: `ρ(X + Y) = ρ(X) + Y` for `Y ∈ 𝒳₁`, `X ∈ 𝒳₂`. -/
def A3 (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) : Prop :=
  ∀ Y ∈ S.X₁, ∀ X : 𝒳, ρ (X + Y) = ρ X + Y

/-- Definition 1, p. 2: a conditional risk mapping `ρ : 𝒳₂ → 𝒳₁` satisfying (A1)–(A3). -/
def IsCondRiskMapping (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) : Prop :=
  MapsToX₁ S ρ ∧ A1 S ρ ∧ A2 S ρ ∧ A3 S ρ

/-- (2.3) Positive homogeneity: `ρ(tX) = tρ(X)` for all `X` and `t > 0`. -/
def PosHomogeneous (ρ : 𝒳 → 𝒳) : Prop := ∀ (t : ℝ) (X : 𝒳), 0 < t → ρ (t • X) = t • ρ X

/-- Lower semicontinuity (p. 4): every `ρ_ω : 𝒳₂ → ℝ` is lower semicontinuous. -/
def IsLsc (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) : Prop :=
  ∀ ω, LowerSemicontinuous (ρω S ρ ω)

/-- The conjugate (3.4): `ρ*(μ, ω) = sup_{X ∈ 𝒳₂} {⟨μ, X⟩ − ρ_ω(X)}`, in `ℝ̄`. -/
noncomputable def conj (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (μ : 𝒴) (ω : Ω) : EReal :=
  ⨆ X : 𝒳, (((pair (S.toMeasure μ) (S.toFun X) - ρω S ρ ω X : ℝ)) : EReal)

/-- `𝒜(ω) = dom ρ*(·, ω) = {μ ∈ 𝒴₂ : ρ*(μ, ω) < +∞}` (the set of (3.8)). -/
def envelope (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (ω : Ω) : Set 𝒴 :=
  {μ | conj S ρ μ ω < ⊤}

/-- Definition 2, p. 8: a selection `ω ↦ μ_ω` is weakly* `ℱ₁`-measurable if
`ω ↦ ⟨μ_ω, X⟩` is `ℱ₁`-measurable for every `X ∈ 𝒳₂`. -/
def IsWeakStarMeasurable (S : PairedSpaces Ω 𝒳 𝒴) (κ : Ω → 𝒴) : Prop :=
  ∀ X, Measurable[S.F₁] fun ω => pair (S.toMeasure (κ ω)) (S.toFun X)

/-- A weakly* `ℱ₁`-measurable selection `μ_ω ∈ 𝒜(ω)`. -/
def IsSelection (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) (κ : Ω → 𝒴) : Prop :=
  (∀ ω, κ ω ∈ envelope S ρ ω) ∧ IsWeakStarMeasurable S κ

/-- (4.4): `[ℚ_μ(ν)](A) = ∫_Ω μ_ω(A) dν(ω)`. -/
noncomputable def QApply (S : PairedSpaces Ω 𝒳 𝒴) (κ : Ω → 𝒴) (ν : 𝒴) (A : Set Ω) : ℝ :=
  pair (S.toMeasure ν) (fun ω => S.toMeasure (κ ω) A)

/-- (4.5): `ν` is a fixed point of `ℚ_μ`: `∫_Ω μ_ω(A) dν(ω) = ν(A)` for every `A ∈ ℱ₂`. -/
def IsFixedPoint (S : PairedSpaces Ω 𝒳 𝒴) (κ : Ω → 𝒴) (ν : 𝒴) : Prop :=
  ∀ A, MeasurableSet A → QApply S κ ν A = S.toMeasure ν A

/-- Assumption (K), p. 10 (closed-graph form): `𝒫_{𝒴₂}` is compact and, for every weakly*
`ℱ₁`-measurable selection `μ_ω ∈ 𝒜(ω)`, the operator `ℚ_μ` maps `𝒫_{𝒴₂}` into itself and has a
closed graph on `𝒫_{𝒴₂}`. Here `q` is `ℚ_μ` on `𝒫_{𝒴₂}`. -/
def CondK (S : PairedSpaces Ω 𝒳 𝒴) (ρ : 𝒳 → 𝒳) : Prop :=
  IsCompact (Prob S) ∧ ∀ κ, IsSelection S ρ κ → ∃ q : 𝒴 → 𝒴,
    Set.MapsTo q (Prob S) (Prob S) ∧
    (∀ ν ∈ Prob S, ∀ A, MeasurableSet A → S.toMeasure (q ν) A = QApply S κ ν A) ∧
    IsClosed {p : 𝒴 × 𝒴 | p.1 ∈ Prob S ∧ p.2 = q p.1}

/-- `μ(·)` is the conditional probability of `ν` with respect to `ℱ₁` (Billingsley, p. 430;
(4.6)): for every `A ∈ ℱ₂`, `ω ↦ μ_ω(A)` is `ℱ₁`-measurable, and
`∫_S μ_ω(A) dν(ω) = ν(A ∩ S)` for all `S ∈ ℱ₁`, `A ∈ ℱ₂`. -/
def IsCondProb (S : PairedSpaces Ω 𝒳 𝒴) (ν : 𝒴) (κ : Ω → 𝒴) : Prop :=
  (∀ A, MeasurableSet A → Measurable[S.F₁] fun ω => S.toMeasure (κ ω) A) ∧
  ∀ A B, MeasurableSet A → MeasurableSet[S.F₁] B →
    pair (S.toMeasure ν) (B.indicator fun ω => S.toMeasure (κ ω) A) = S.toMeasure ν (A ∩ B)

/-- `ω ↦ μ_ω` is a probability-valued, weakly* `ℱ₁`-measurable conditional probability of the
probability measure `ν` given `ℱ₁`; then `⟨μ_ω, X⟩ = 𝔼_ν[X | ℱ₁](ω)`. -/
def IsCondExpKernel (S : PairedSpaces Ω 𝒳 𝒴) (ν : 𝒴) (κ : Ω → 𝒴) : Prop :=
  ν ∈ Prob S ∧ (∀ ω, κ ω ∈ Prob S) ∧ IsWeakStarMeasurable S κ ∧ IsCondProb S ν κ

end CondRiskMap.Repr


