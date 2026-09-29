-- Prove2me | Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
-- name    : CondConvexRisk_Representation_CondConvexRiskMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:52:56.352943+00:00
-- url     : https://prove2.me/theorems/213475fd-83d5-4817-bc7f-ea4effe32bfa
-- title:
--   Definition 2.2 — conditional convex risk measure; the model set $\mathcal P_{\mathcal G}$
-- statement:
--   Fix a probability space $(\Omega,\mathcal F,P)$ and a sub-$\sigma$-algebra $\mathcal G\subseteq\mathcal F$. Let $L^\infty$ be the essentially bounded random variables and $L^\infty_{\mathcal G}$ the $\mathcal G$-measurable ones; all (in)equalities between random variables hold $P$-almost surely.
--
--   The set of admissible probabilistic models is
--   $$\mathcal P_{\mathcal G}=\{Q \text{ probability measure on }(\Omega,\mathcal F) : Q\ll P \text{ on } \mathcal F,\ Q(A)=P(A)\ \text{for all } A\in\mathcal G\}.$$
--
--   A map $\rho:L^\infty\to L^\infty_{\mathcal G}$ is a **conditional convex risk measure** if
--   1. (conditional translation invariance) $\rho(X+Z)=\rho(X)-Z$ for all $X\in L^\infty$, $Z\in L^\infty_{\mathcal G}$;
--   2. (monotonicity) $X\le Y$ implies $\rho(X)\ge\rho(Y)$;
--   3. (conditional convexity) $\rho(\Lambda X+(1-\Lambda)Y)\le\Lambda\rho(X)+(1-\Lambda)\rho(Y)$ for all $X,Y\in L^\infty$ and $\Lambda\in L^\infty_{\mathcal G}$ with $0\le\Lambda\le1$;
--   4. (normalization) $\rho(0)=0$.
--
--   The quantity $\rho(X)(\omega)$ is the riskiness of the payoff $X$ given the information $\mathcal G$; when $\mathcal G$ is trivial the notion reduces to an ordinary convex risk measure.
--
--   **Formalization Note** Payoffs are real functions with `MemLp X ⊤ P`; $\rho$ acts on functions, so it is required to respect $P$-a.s. equality (the paper works with equivalence classes), and for each $X\in L^\infty$ the value $\rho(X)$ is a $\mathcal G$-strongly measurable essentially bounded function. Translation invariance and convexity quantify over $\mathcal G$-measurable $Z$, $\Lambda$, not over constants. $\mathcal P_{\mathcal G}$ is the subtype `PG m P`; "$Q\equiv P$ on $\mathcal G$" is equality of the measures on $\mathcal G$, not mutual absolute continuity.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 3 (sets P and P_G; the three axioms) and p. 4, Definition 2.2

import Mathlib

open MeasureTheory

namespace CondConvexRisk.Representation

/-- Section 2, p. 3: the set `P_G` of probability measures `Q` on `(Ω, F)` with `Q ≪ P` on `F`
and `Q ≡ P` on `G`, i.e. `Q(A) = P(A)` for every `A ∈ G`.  Here `F` is the ambient σ-algebra
`mΩ` and `G` is the sub-σ-algebra `m`. -/
def PG {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) :
    Type _ :=
  {Q : Measure[mΩ] Ω // IsProbabilityMeasure Q ∧ Q ≪ P ∧ ∀ A, MeasurableSet[m] A → Q A = P A}

/-- Definition 2.2, p. 4 (with the three axioms of p. 3): `ρ : L∞ → L∞_G` is a conditional
convex risk measure.  Payoffs are real functions with `MemLp X ∞ P`; `ρ` acts on functions, so
it is required to respect `P`-a.s. equality (the paper works on equivalence classes), and its
value on each `X ∈ L∞` is a `G`-measurable essentially bounded function.  All (in)equalities
between random variables are `P`-a.s.  `ρ` is unconstrained outside `L∞`. -/
structure IsCondConvexRiskMeasure {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) : Prop where
  /-- `ρ` is well defined on `P`-equivalence classes. -/
  ae_congr : ∀ X Y : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → X =ᵐ[P] Y → ρ X =ᵐ[P] ρ Y
  /-- `ρ(X)` is `G`-measurable. -/
  stronglyMeasurable : ∀ X : Ω → ℝ, MemLp X ⊤ P → StronglyMeasurable[m] (ρ X)
  /-- `ρ(X)` is essentially bounded. -/
  memLp : ∀ X : Ω → ℝ, MemLp X ⊤ P → MemLp (ρ X) ⊤ P
  /-- (Conditional) translation invariance: `ρ(X + Z) = ρ(X) - Z` for `Z ∈ L∞_G`. -/
  translation : ∀ X Z : Ω → ℝ, MemLp X ⊤ P → MemLp Z ⊤ P → StronglyMeasurable[m] Z →
    ρ (X + Z) =ᵐ[P] ρ X - Z
  /-- Monotonicity: `X ≤ Y` implies `ρ(X) ≥ ρ(Y)`. -/
  monotone : ∀ X Y : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → X ≤ᵐ[P] Y → ρ Y ≤ᵐ[P] ρ X
  /-- (Conditional) convexity with `G`-measurable weights `0 ≤ Λ ≤ 1`. -/
  convex : ∀ X Y Λ : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → StronglyMeasurable[m] Λ →
    (∀ᵐ ω ∂P, 0 ≤ Λ ω ∧ Λ ω ≤ 1) →
    ρ (Λ * X + (1 - Λ) * Y) ≤ᵐ[P] Λ * ρ X + (1 - Λ) * ρ Y
  /-- Normalization: `ρ(0) = 0`. -/
  map_zero : ρ 0 =ᵐ[P] 0

end CondConvexRisk.Representation


