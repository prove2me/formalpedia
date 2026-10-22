-- Prove2me | Definitions.Def_RiskFunctionals_Kusuoka_Functionals
-- name    : RiskFunctionals_Kusuoka_Functionals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:55.904982+00:00
-- url     : https://prove2.me/theorems/b1be8617-1800-4ae8-8507-a398005b3c5e
-- title:
--   Non-atomic spaces, version-independence, acceptability functionals and dual representations on $L_p$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $1\le p\le\infty$, with $L_p=L_p(\Omega,\mathcal F,\mathbb P)$ the space of (classes of almost surely equal) real random variables with finite $p$-th moment.
--
--   1. A measurable set $A$ is an **atom** of $\mathbb P$ if $\mathbb P(A)>0$ and every measurable $A'\subseteq A$ has $\mathbb P(A')=\mathbb P(A)$ or $\mathbb P(A')=0$; the space is **non-atomic** if $\mathbb P$ has no atoms.
--   2. A functional $\mathcal R:L_p\to\mathbb R$ is **version-independent** if $Y^{(1)}\overset{d}{=}Y^{(2)}$ (equal distributions) implies $\mathcal R(Y^{(1)})=\mathcal R(Y^{(2)})$.
--   3. A real valued $\mathcal A:L_p\to\mathbb R$ is an **acceptability functional** if
--      - (A1) $\mathcal A(Y+c)=\mathcal A(Y)+c$ for all constants $c\in\mathbb R$;
--      - (A2) $\mathcal A(\lambda Y^{(1)}+(1-\lambda)Y^{(2)})\ge\lambda\mathcal A(Y^{(1)})+(1-\lambda)\mathcal A(Y^{(2)})$ for $0\le\lambda\le1$;
--      - (A3) $Y^{(1)}\le Y^{(2)}$ a.s. implies $\mathcal A(Y^{(1)})\le\mathcal A(Y^{(2)})$.
--   4. Given a set $\mathcal Z_{\mathcal A}\subseteq L_q$ and a real function $\bar A$ on $L_q$, $\mathcal A$ has the **dual representation**
--   $$\mathcal A(Y)=\inf\{\mathbb E(YZ)-\bar A(Z) : Z\in\mathcal Z_{\mathcal A}\}\qquad\text{for every }Y\in L_p,$$
--   meaning that for each $Y$ the set $\{\mathbb E(YZ)-\bar A(Z): Z\in\mathcal Z_{\mathcal A}\}$ is nonempty, bounded below, and has infimum $\mathcal A(Y)$.
--   5. The pair $(\bar A,\mathcal Z_{\mathcal A})$ is **version-independent** if whenever $Z$ and $\tilde Z$ have the same distribution, either both or none lie in $\mathcal Z_{\mathcal A}$, and $\bar A(Z)=\bar A(\tilde Z)$ when they do.
--
--   These are the standing notions of Theorem 2.45 (Kusuoka representations) and of Theorem 2.30.
--
--   **Formalization Note** Non-atomicity is the book's Appendix A notion, which is stronger than "every singleton is null". The dual function is written $\bar A$ here to distinguish it from the functional $\mathcal A$; the book calls it $A$. The book allows $A(Z)=-\infty$ and restricts to $\mathcal Z_{\mathcal A}=\{A>-\infty\}$; here $\bar A$ is real valued and only its values on $\mathcal Z_{\mathcal A}$ enter. In the dual representation, $\mathbb E(YZ)=\int YZ\,d\mathbb P$ is meant for $Z\in L_q$ with $q$ the conjugate exponent, where it is finite; the definition itself takes $p,q$ as parameters, and every theorem of the mission assumes $1/p+1/q=1$. The infimum is expressed as "greatest lower bound in $\mathbb R$", which forces the set to be nonempty and bounded below.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 265 (atoms, non-atomic), p. 28 Definition 2.1, pp. 35–36 Definition 2.17, p. 42 Eq. (2.8), p. 43 Theorem 2.30(iii), p. 59 Theorem 2.45

import Mathlib

namespace RiskFunctionals.Kusuoka

open MeasureTheory ProbabilityTheory

/-- An atom of `P` (Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific
2007, p. 265, Appendix A): a measurable set `A` with `P(A) > 0` such that every measurable
`A' ⊆ A` has `P(A') = P(A)` or `P(A') = 0`. -/
def IsAtomOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ 0 < P A ∧ ∀ A' ⊆ A, MeasurableSet A' → P A' = P A ∨ P A' = 0

/-- A non-atomic probability space (p. 265: "A probability space is called non-atomic if `P` has
no atoms"). This is stronger than Mathlib's `NoAtoms`, which only asks singletons to be null. -/
def IsNonAtomic {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Prop :=
  ∀ A : Set Ω, ¬ IsAtomOf P A

/-- Version-independence (p. 28, Definition 2.1) of a real functional `ℛ` on `L_p(Ω, ℱ, P)`:
`Y⁽¹⁾ =ᵈ Y⁽²⁾` implies `ℛ(Y⁽¹⁾) = ℛ(Y⁽²⁾)`. -/
def IsVersionIndependent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ENNReal}
    (R : Lp ℝ p P → ℝ) : Prop :=
  ∀ Y₁ Y₂ : Lp ℝ p P, IdentDistrib (Y₁ : Ω → ℝ) (Y₂ : Ω → ℝ) P P → R Y₁ = R Y₂

/-- An acceptability functional (pp. 35–36, Definition 2.17): a real valued mapping `𝒜` on
`L_p(Ω, ℱ, P)` with
(A1) translation equivariance `𝒜(Y + c) = 𝒜(Y) + c` for all constants `c`,
(A2) concavity `𝒜(λY⁽¹⁾ + (1 − λ)Y⁽²⁾) ≥ λ𝒜(Y⁽¹⁾) + (1 − λ)𝒜(Y⁽²⁾)` for `0 ≤ λ ≤ 1`,
(A3) monotonicity: `Y⁽¹⁾ ≤ Y⁽²⁾` a.s. implies `𝒜(Y⁽¹⁾) ≤ 𝒜(Y⁽²⁾)`. -/
structure IsAcceptabilityFunctional {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {p : ENNReal} (A : Lp ℝ p P → ℝ) : Prop where
  translationEquivariant : ∀ (Y : Lp ℝ p P) (c : ℝ), A (Y + Lp.const p P c) = A Y + c
  concave : ∀ (Y₁ Y₂ : Lp ℝ p P) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    lam * A Y₁ + (1 - lam) * A Y₂ ≤ A (lam • Y₁ + (1 - lam) • Y₂)
  monotone : ∀ Y₁ Y₂ : Lp ℝ p P, (∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) → A Y₁ ≤ A Y₂

/-- The dual representation (p. 42, (2.8); p. 59, Theorem 2.45)
`𝒜(Y) = inf {𝔼(Y Z) − A(Z) : Z ∈ 𝒵_𝒜 ⊆ 𝒵}` for every `Y ∈ L_p`, where `𝒵 = L_q` is the dual
space and `A` is real valued on `𝒵_𝒜` (p. 43: `𝒵_𝒜 = {Z : A(Z) > −∞}`; values of `A` outside
`𝒵_𝒜` play no role). The infimum is the greatest lower bound in `ℝ`: the set is nonempty, bounded
below, and `𝒜(Y)` is its infimum. -/
def HasDualRepresentation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p q : ENNReal}
    (𝒜 : Lp ℝ p P → ℝ) (𝒵𝒜 : Set (Lp ℝ q P)) (A : Lp ℝ q P → ℝ) : Prop :=
  ∀ Y : Lp ℝ p P, IsGLB {x : ℝ | ∃ Z ∈ 𝒵𝒜, x = (∫ ω, Y ω * Z ω ∂P) - A Z} (𝒜 Y)

/-- Version-independence of the dual function `A` together with its domain `𝒵_𝒜`
(p. 43, Theorem 2.30(iii)): if `Z` and `Z̃` have the same distribution then either both or none
is in `𝒵_𝒜`, and `A(Z) = A(Z̃)` when they are. -/
def IsVersionIndependentDual {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {q : ENNReal}
    (𝒵𝒜 : Set (Lp ℝ q P)) (A : Lp ℝ q P → ℝ) : Prop :=
  ∀ Z₁ Z₂ : Lp ℝ q P, IdentDistrib (Z₁ : Ω → ℝ) (Z₂ : Ω → ℝ) P P →
    (Z₁ ∈ 𝒵𝒜 ↔ Z₂ ∈ 𝒵𝒜) ∧ (Z₁ ∈ 𝒵𝒜 → A Z₁ = A Z₂)

end RiskFunctionals.Kusuoka


