-- Prove2me | Definitions.Def_RiskFunctionals_MultiPeriod_DualExtension
-- name    : RiskFunctionals_MultiPeriod_DualExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:26.327992+00:00
-- url     : https://prove2.me/theorems/3a0349bc-5beb-4bd1-976f-af66c1d24059
-- title:
--   The dual extension $\mathcal A(Y;\mathcal F_1)$ of a single-period acceptability functional, information monotonicity and concave dominance
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $p\in[1,\infty]$ and $1/p+1/q=1$. Let $A$ be a functional on $L_q$ with values in $[-\infty,+\infty]$, and let $\mathcal Z_{\mathcal A}=\{Z\in L_q:A(Z)>-\infty\}$ be its **supergradient set** (risk envelope, p. 43).
--
--   1. The single-period functional in **dual form** is
--   $$\mathcal A(Y)=\inf\{\mathbb E(YZ)-A(Z):\mathbb E(Z)=1,\ Z\in\mathcal Z_{\mathcal A}\},\qquad Y\in L_p.\tag{3.7}$$
--   2. Its **dual extension** to a sub-σ-algebra $\mathcal F_1\subseteq\mathcal F$ is
--   $$\mathcal A(Y;\mathcal F_1)=\inf\{\mathbb E(YZ)-A(Z):\mathbb E(Z\mid\mathcal F_1)=1,\ Z\in\mathcal Z_{\mathcal A}\}.\tag{3.8}$$
--   3. A functional $\mathcal A(Y;\mathcal F_1)$ that depends on a σ-algebra is **information monotone** (A0) if $\mathcal F_1'\subseteq\mathcal F_1$ implies $\mathcal A(Y;\mathcal F_1')\le\mathcal A(Y;\mathcal F_1)$.
--   4. A random variable $Y^{(1)}$ is dominated by $Y^{(2)}$ in the **concave order**, $Y^{(1)}\prec_{CCD}Y^{(2)}$, if $\mathbb E[U(Y^{(1)})]\le\mathbb E[U(Y^{(2)})]$ for every concave $U:\mathbb R\to\mathbb R$ for which both expectations exist.
--   5. A functional $A$ on $L_q$ is **isotonic w.r.t. concave dominance** if $Z^{(1)}\prec_{CCD}Z^{(2)}$ implies $A(Z^{(1)})\le A(Z^{(2)})$.
--
--   The dual extension is one of the two ways the book introduces information into a single-period functional (§3.1.3.2). The expected conditional average value-at-risk (3.9) is an instance.
--
--   **Formalization Note** $\mathcal Z_{\mathcal A}$ is not a free parameter: it is the supergradient set of $A$, as the book defines the symbol on p. 43. Both infima are taken in `EReal`. On an empty constraint set they are $+\infty$. The σ-algebra $\mathcal F_1$ is an argument of type `MeasurableSpace Ω`, and the statements that use it assume $\mathcal F_1\le\mathcal F$. Conditional expectation is Mathlib's `condExp`, and "$\mathbb E(Z\mid\mathcal F_1)=1$" holds $P$-a.s. "For which the expectations exist" is read as integrability of $U(Y^{(1)})$ and $U(Y^{(2)})$. Concave dominance duplicates Definition 1.10(iii) of chapter 1 and isotonicity duplicates Definition 2.9(iii) of chapter 2; both are separate drafts there.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 129, Eqs. (3.7)–(3.8); p. 127, Definition 3.6; p. 13, Definition 1.10(iii); p. 32, Definition 2.9(iii)

import Mathlib

namespace RiskFunctionals.MultiPeriod

open MeasureTheory

/-- The supergradient set (risk envelope) `𝒵_𝒜 = {Z ∈ 𝒵 : A(Z) > −∞}` of a functional `A` on
`𝒵 = L_q` (Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007,
p. 43). -/
def supergradientSet {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure[m0] Ω} {q : ENNReal}
    (A : Lp ℝ q P → EReal) : Set (Lp ℝ q P) :=
  {Z | ⊥ < A Z}

/-- A single-period acceptability functional in the dual form (3.7) (p. 129):
`𝒜(Y) = inf{𝔼(Y Z) − A(Z) : 𝔼(Z) = 1, Z ∈ 𝒵_𝒜}` on `𝒴 = L_p(Ω, ℱ, P)`, for a functional
`A : L_q → ℝ̄` with supergradient set `𝒵_𝒜 = {A > −∞}` (p. 43), as an infimum in `EReal`. -/
noncomputable def dualForm {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure[m0] Ω} {p q : ENNReal}
    (A : Lp ℝ q P → EReal) (Y : Lp ℝ p P) : EReal :=
  ⨅ Z ∈ {Z : Lp ℝ q P | Z ∈ supergradientSet A ∧ ∫ ω, (Z : Ω → ℝ) ω ∂P = 1},
    ((∫ ω, (Y : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P : ℝ) : EReal) - A Z

/-- The dual extension (3.8) (p. 129) of a functional of the form (3.7) to a σ-algebra `ℱ₁`:
`𝒜(Y; ℱ₁) = inf{𝔼(Y Z) − A(Z) : 𝔼(Z | ℱ₁) = 1, Z ∈ 𝒵_𝒜}`, an infimum in `EReal`, with
`𝒵_𝒜 = {A > −∞}` (p. 43). The σ-algebra `ℱ₁` is the argument `m₁`; the statements using it take
`m₁ ≤ ℱ`. -/
noncomputable def dualExtension {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure[m0] Ω}
    {p q : ENNReal} (A : Lp ℝ q P → EReal) (m₁ : MeasurableSpace Ω)
    (Y : Lp ℝ p P) : EReal :=
  ⨅ Z ∈ {Z : Lp ℝ q P | Z ∈ supergradientSet A ∧
      condExp m₁ P (Z : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ)},
    ((∫ ω, (Y : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P : ℝ) : EReal) - A Z

/-- Definition 3.6 (p. 127), (A0) information monotonicity of an information-dependent
functional `𝒜(Y; ℱ₁)`: if `ℱ′₁ ⊆ ℱ₁` (both sub-σ-algebras of `ℱ`) then
`𝒜(Y; ℱ′₁) ≤ 𝒜(Y; ℱ₁)`. -/
def IsInformationMonotoneSP {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure[m0] Ω} {p : ENNReal}
    (A : MeasurableSpace Ω → Lp ℝ p P → EReal) : Prop :=
  ∀ m₁' m₁ : MeasurableSpace Ω, m₁' ≤ m₁ → m₁ ≤ m0 → ∀ Y : Lp ℝ p P, A m₁' Y ≤ A m₁ Y

/-- Concave dominance (p. 13, Definition 1.10(iii)): `Y⁽¹⁾ ≺_CCD Y⁽²⁾` if
`𝔼[U(Y⁽¹⁾)] ≤ 𝔼[U(Y⁽²⁾)]` for all concave `U` for which the integrals exist. -/
def ConcaveDominated {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ U : ℝ → ℝ, ConcaveOn ℝ Set.univ U → Integrable (fun ω => U (X ω)) P →
    Integrable (fun ω => U (Y ω)) P → ∫ ω, U (X ω) ∂P ≤ ∫ ω, U (Y ω) ∂P

/-- Isotonicity w.r.t. concave dominance (p. 32, Definition 2.9(iii)) of a functional `A` on
`L_q`: `Z⁽¹⁾ ≺_CCD Z⁽²⁾` implies `A(Z⁽¹⁾) ≤ A(Z⁽²⁾)`. -/
def IsIsotonicCCD {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {q : ENNReal}
    (A : Lp ℝ q P → EReal) : Prop :=
  ∀ Z₁ Z₂ : Lp ℝ q P, ConcaveDominated P (Z₁ : Ω → ℝ) (Z₂ : Ω → ℝ) → A Z₁ ≤ A Z₂

end RiskFunctionals.MultiPeriod


