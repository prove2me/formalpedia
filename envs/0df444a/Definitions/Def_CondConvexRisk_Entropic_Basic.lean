-- Prove2me | Definitions.Def_CondConvexRisk_Entropic_Basic
-- name    : CondConvexRisk_Entropic_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:59:44.649135+00:00
-- url     : https://prove2.me/theorems/ddc05285-976f-4ae4-a61a-6dc24d64c536
-- title:
--   Section 2–3 and Appendix A — P_G, conditional convex risk measures, essential supremum/infimum, minimal penalty
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\mathcal G\subseteq\mathcal F$ a sub-$\sigma$-algebra. $L^\infty$ denotes the essentially bounded random variables and $L^\infty_{\mathcal G}$ the $\mathcal G$-measurable ones; all (in)equalities between random variables hold $P$-almost surely.
--
--   1. $\mathcal P_{\mathcal G}$ is the set of probability measures $Q$ on $(\Omega,\mathcal F)$ with $Q\ll P$ and $Q(A)=P(A)$ for every $A\in\mathcal G$.
--   2. A map $\rho:L^\infty\to L^\infty_{\mathcal G}$ is a **conditional convex risk measure** if it is translation invariant ($\rho(X+Z)=\rho(X)-Z$ for $Z\in L^\infty_{\mathcal G}$), monotone ($X\le Y\Rightarrow \rho(X)\ge\rho(Y)$), conditionally convex ($\rho(\Lambda X+(1-\Lambda)Y)\le\Lambda\rho(X)+(1-\Lambda)\rho(Y)$ for $\Lambda\in L^\infty_{\mathcal G}$, $0\le\Lambda\le1$) and satisfies $\rho(0)=0$.
--   3. For a family $\mathcal X$ of $[-\infty,+\infty]$-valued random variables, $Z=\operatorname{ess.sup}\mathcal X$ if $Z\ge X$ for all $X\in\mathcal X$ and $Z\le W$ for every $W$ with this property; $\operatorname{ess.inf}$ is defined symmetrically.
--   4. $\rho$ is **continuous from above** if $X_n\searrow X$ in $L^\infty$ implies $\rho(X_n)\nearrow\rho(X)$.
--   5. The **minimal penalty** of $\rho$ is
--   $$\alpha^*(Q)=\operatorname{ess.sup}_{X\in L^\infty}\{-E_Q(X\mid\mathcal G)-\rho(X)\},\qquad Q\in\mathcal P_{\mathcal G}.$$
--
--   These are the standing objects of the paper on which the conditional entropic risk measure and its robust representation are stated.
--
--   **Formalization Note** Payoffs are real functions with `MemLp X ⊤ P`; `ρ` acts on functions and must respect $P$-a.s. equality on $L^\infty$. $L^\infty_{\mathcal G}$ membership is `StronglyMeasurable[m]` plus `MemLp ⊤`. Essential suprema/infima are predicates `IsEssSup`/`IsEssInf` on a candidate $P$-a.e. measurable `EReal`-valued function, never a pointwise supremum. $E_Q(\cdot\mid\mathcal G)$ is Mathlib's conditional expectation under $Q$.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 3–4 (setting, axioms, Definition 2.2), p. 6 (Theorem 3.2 (a),(c): continuity from above, minimal penalty), p. 19 (Appendix A, ess.sup / ess.inf)

import Mathlib

open MeasureTheory Filter Topology

namespace CondConvexRisk.Entropic

/-- Section 2, p. 3: the set `P_G` of probability measures `Q` on `(Ω, F)` with `Q ≪ P` on `F`
and `Q ≡ P` on `G`, i.e. `Q(A) = P(A)` for every `A ∈ G`.  Here `F` is the ambient σ-algebra
`mΩ` and `G` is the sub-σ-algebra `m`. -/
def PG {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) :
    Type _ :=
  {Q : Measure[mΩ] Ω // IsProbabilityMeasure Q ∧ Q ≪ P ∧ ∀ A, MeasurableSet[m] A → Q A = P A}

/-- The space `L∞` of payoffs, as the subtype of real functions with `MemLp X ∞ P`. -/
abbrev LInf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Type _ :=
  {X : Ω → ℝ // MemLp X ⊤ P}

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

/-- Appendix A, p. 19: `Z` is an essential supremum of the family `F` of extended random
variables with respect to `P`: `Z` is an a.s. upper bound of every member, and it is a.s. below
every (a.e.-measurable) a.s. upper bound of the family.  Elements of `L⁰(ℝ̄)` are represented by
`P`-a.e. measurable functions `Ω → EReal`; every (in)equality is `P`-a.s. -/
def IsEssSup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal)
    (Z : Ω → EReal) : Prop :=
  AEMeasurable Z P ∧ (∀ i, F i ≤ᵐ[P] Z) ∧
    ∀ W : Ω → EReal, AEMeasurable W P → (∀ i, F i ≤ᵐ[P] W) → Z ≤ᵐ[P] W

/-- Appendix A, p. 19: `Z` is an essential infimum of the family `F`
(`ess.inf 𝒳 = -ess.sup(-𝒳)`, written out): `Z` is an a.s. lower bound of every member, and it
is a.s. above every (a.e.-measurable) a.s. lower bound of the family. -/
def IsEssInf {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal)
    (Z : Ω → EReal) : Prop :=
  AEMeasurable Z P ∧ (∀ i, Z ≤ᵐ[P] F i) ∧
    ∀ W : Ω → EReal, AEMeasurable W P → (∀ i, W ≤ᵐ[P] F i) → W ≤ᵐ[P] Z

/-- Theorem 3.2 (a), p. 6: `ρ` is continuous from above: whenever `X_n, X ∈ L∞` and
`X_n ↘ X` `P`-a.s. (a.s. non-increasing and a.s. convergent to `X`), then `ρ(X_n) ↗ ρ(X)`
`P`-a.s. (a.s. non-decreasing and a.s. convergent to `ρ(X)`). -/
def IsContinuousFromAbove {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∀ (X : ℕ → Ω → ℝ) (Y : Ω → ℝ), (∀ n, MemLp (X n) ⊤ P) → MemLp Y ⊤ P →
    (∀ᵐ ω ∂P, Antitone (fun n => X n ω) ∧ Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) →
    ∀ᵐ ω ∂P, Monotone (fun n => ρ (X n) ω) ∧ Tendsto (fun n => ρ (X n) ω) atTop (𝓝 (ρ Y ω))

/-- The family `{-E_Q(X | G) - ρ(X) | X ∈ L∞}` (p. 7), indexed by `X ∈ L∞`, whose essential
supremum is the minimal penalty `α*(Q)` of Theorem 3.2 (c), p. 6.  `E_Q(X | G)` is Mathlib's
conditional expectation `Q[X | m]` (well defined: `X` is `Q`-integrable since `Q ≪ P`). -/
noncomputable def penaltyFamily {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) (Q : PG m P) : LInf P → Ω → EReal :=
  fun X ω => ((-(Q.1[X.1 | m]) ω - ρ X.1 ω : ℝ) : EReal)

/-- Theorem 3.2 (c), p. 6: `α*` is the minimal penalty of `ρ`,
`α*(Q) = ess.sup_{X ∈ L∞} {-E_Q(X | G) - ρ(X)}` for every `Q ∈ P_G`.  A predicate on a
candidate `α*`. -/
def IsMinimalPenalty {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) (α : PG m P → Ω → EReal) : Prop :=
  ∀ Q : PG m P, IsEssSup P (penaltyFamily m P ρ Q) (α Q)

end CondConvexRisk.Entropic


