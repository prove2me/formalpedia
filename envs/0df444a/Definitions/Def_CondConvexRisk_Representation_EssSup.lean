-- Prove2me | Definitions.Def_CondConvexRisk_Representation_EssSup
-- name    : CondConvexRisk_Representation_EssSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:52:33.808966+00:00
-- url     : https://prove2.me/theorems/c94016e4-d1ba-428e-9d23-c1f7252a0507
-- title:
--   Appendix A — essential supremum of a family, upward directed families, extended expectation
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and let $L^0(\bar{\mathbb R})$ be the space of (classes of) $\mathcal F$-measurable random variables with values in $\bar{\mathbb R}=[-\infty,+\infty]$, ordered $P$-almost surely. For a family $\mathcal X=\{X_i\}_{i\in I}\subseteq L^0(\bar{\mathbb R})$ let
--   $$D(\mathcal X)=\{Z\in L^0(\bar{\mathbb R}) : Z\ge X_i \ P\text{-a.s. for all } i\in I\}.$$
--
--   1. $Z$ is an **essential supremum** of $\mathcal X$, written $Z=\operatorname{ess.sup}\mathcal X$, if $Z\in D(\mathcal X)$ and $Z\le W$ $P$-a.s. for every $W\in D(\mathcal X)$.
--   2. $\mathcal X$ is **upward directed** if for all $i,j\in I$ there is $k\in I$ with $X_k\ge\max(X_i,X_j)$ $P$-a.s.
--   3. For $Z\in L^0(\bar{\mathbb R})$ write $E_P[Z^+]=\int Z^+\,dP$ and $E_P[Z^-]=\int Z^-\,dP$, both in $[0,+\infty]$. The **expectation of $Z$ exists** if these are not both $+\infty$, and then $E_P[Z]=E_P[Z^+]-E_P[Z^-]\in[-\infty,+\infty]$.
--
--   These are the objects of the appendix of the paper, on which the robust representation of conditional risk measures is built: the supremum over an uncountable family of probability models is taken in the essential sense.
--
--   **Formalization Note** Elements of $L^0(\bar{\mathbb R})$ are functions $\Omega\to$ `EReal`; the essential supremum is a predicate `IsEssSup P F Z` on a candidate $Z$ (existence and a.s. uniqueness are Theorem A.1), not a pointwise supremum. $Z$ and the competitors $W$ are required to be $P$-a.e. measurable. `expectation` is only meaningful under `HasExpectation` (otherwise `EReal` gives $+\infty-(+\infty)=-\infty$).
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 19, Appendix A (definition of D(X), ess.sup, upward directed; extended expectation)

import Mathlib

open MeasureTheory

namespace CondConvexRisk.Representation

/-- Appendix A, p. 19: `Z` is an essential supremum of the family `F` of extended random
variables with respect to `P`.  `Z` lies in `D(F)` (it is an a.s. upper bound of every member)
and it is a.s. below every element of `D(F)`.  Elements of `L⁰(ℝ̄)` are represented by
`P`-a.e. measurable functions `Ω → EReal`; every (in)equality is `P`-a.s. -/
def IsEssSup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal)
    (Z : Ω → EReal) : Prop :=
  AEMeasurable Z P ∧ (∀ i, F i ≤ᵐ[P] Z) ∧
    ∀ W : Ω → EReal, AEMeasurable W P → (∀ i, F i ≤ᵐ[P] W) → Z ≤ᵐ[P] W

/-- Appendix A, p. 19: the family `F` is upward directed, i.e. for any two members there is a
member that is `P`-a.s. above both (equivalently, above their maximum). -/
def IsUpwardDirected {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal) :
    Prop :=
  ∀ i j, ∃ k, F i ≤ᵐ[P] F k ∧ F j ≤ᵐ[P] F k

/-- Positive part `E_P[Z⁺] ∈ [0, +∞]` of an extended random variable. -/
noncomputable def posExpectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → EReal) : ENNReal :=
  ∫⁻ ω, (Z ω).toENNReal ∂P

/-- Negative part `E_P[Z⁻] ∈ [0, +∞]` of an extended random variable. -/
noncomputable def negExpectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → EReal) : ENNReal :=
  ∫⁻ ω, (-Z ω).toENNReal ∂P

/-- The expectation of an extended random variable exists: `E_P[Z⁺]` and `E_P[Z⁻]` are not
both `+∞`. -/
def HasExpectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → EReal) : Prop :=
  posExpectation P Z ≠ ⊤ ∨ negExpectation P Z ≠ ⊤

/-- The (extended) expectation `E_P[Z] = E_P[Z⁺] - E_P[Z⁻] ∈ [-∞, +∞]`.  It is meaningful
only under `HasExpectation P Z` (otherwise `⊤ - ⊤ = ⊥` in `EReal`). -/
noncomputable def expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → EReal) : EReal :=
  (posExpectation P Z : EReal) - (negExpectation P Z : EReal)

end CondConvexRisk.Representation


