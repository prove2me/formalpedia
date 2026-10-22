-- Prove2me | Definitions.Def_RiskFunctionals_Conditional_Mappings
-- name    : RiskFunctionals_Conditional_Mappings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:04.332417+00:00
-- url     : https://prove2.me/theorems/06661462-f299-4781-813b-1a98f99b29dd
-- title:
--   Conditional acceptability mappings (CA1)–(CA3), positive homogeneity, upper semicontinuity, and the dual function $A_B$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $\mathcal F_1\subseteq\mathcal F$ a sub-$\sigma$-field (the **observable information**). Fix $p\in[1,\infty)$ and put $\mathcal Y=L_p(\Omega,\mathcal F,\mathbb P)$ and $\mathcal Y_1=L_p(\Omega,\mathcal F_1,\mathbb P)$, the subspace of classes in $\mathcal Y$ having an $\mathcal F_1$-measurable version. Random variables that agree almost surely are identified, and every (in)equality between them is meant $\mathbb P$-almost surely.
--
--   1. A mapping $\mathcal A:\mathcal Y\to\mathcal Y_1$ is a **conditional acceptability mapping** if for all $Y,\tilde Y\in\mathcal Y$:
--      - (CA1) predictable translation-equivariance: $\mathcal A(Y+Y^{(1)})=\mathcal A(Y)+Y^{(1)}$ for every $Y^{(1)}\in\mathcal Y_1$;
--      - (CA2) concavity: $\mathcal A(\lambda Y+(1-\lambda)\tilde Y)\ge\lambda\mathcal A(Y)+(1-\lambda)\mathcal A(\tilde Y)$ for all $\lambda\in[0,1]$;
--      - (CA3) monotonicity: $Y\le\tilde Y$ implies $\mathcal A(Y)\le\mathcal A(\tilde Y)$.
--   2. $\mathcal A$ is **positively homogeneous** if $\mathcal A(\lambda Y)=\lambda\mathcal A(Y)$ for every $\lambda>0$.
--   3. $\mathcal A$ is **upper semicontinuous** if for every $B\in\mathcal F_1$ the real functional $Y\mapsto\mathbb E(\mathcal A(Y)\mathbb 1_B)$ is upper semicontinuous on $\mathcal Y$ (norm topology).
--   4. For $Y\in\mathcal Y$ and $Z\in L_q(\Omega,\mathcal F,\mathbb P)$ the **pairing** is $\mathbb E(YZ)=\int_\Omega YZ\,d\mathbb P$.
--   5. For $B\in\mathcal F_1$ and $Z\in L_q(\mathcal F)$ the **dual function** is
--   $$A_B(Z)=\inf\{\mathbb E(YZ)-\mathbb E(\mathcal A(Y)\mathbb 1_B):Y\in\mathcal Y\}\in[-\infty,+\infty],\tag{2.46}$$
--   and $S_B=\{Z\in L_q(\mathcal F):A_B(Z)\ge0\}$.
--   6. $Z\in L_q(\mathcal F)$ is a **conditional density for $B$** if $Z\ge0$ and $\mathbb E(Z\mid\mathcal F_1)=\mathbb 1_B$.
--   7. For a set $S\subseteq L_\infty(\mathcal F)$ and $Y\in L_1(\mathcal F)$, a class $Y_1^*\in L_1(\mathcal F_1)$ **satisfies the dual relation (2.50)** if for every $B\in\mathcal F_1$
--   $$\mathbb E(Y_1^*\mathbb 1_B)=\inf_{Z\in S}\{\mathbb E(YZ):Z\ge0,\ \mathbb E(Z\mid\mathcal F_1)=\mathbb 1_B\}.$$
--
--   These are the objects of §2.3 of the book: conditional acceptability mappings generalize acceptability functionals by returning an $\mathcal F_1$-measurable random variable instead of a number, and the dual function and the dual relation are the two halves of their representation theory.
--
--   **Formalization Note** $\mathcal Y$ is `Lp ℝ p P` and $\mathcal Y_1$ is Mathlib's subspace `lpMeas ℝ ℝ m p P` of classes that are a.e. equal to an `m`-measurable function, where `m` is $\mathcal F_1$ and the ambient measurable space is $\mathcal F$; theorems assume `m ≤ mΩ`. (CA1)–(CA3) and positive homogeneity are stated pointwise almost everywhere on representatives. The book prints (CA1) as $\mathcal A(Y+Y^1)$, a typo for $Y^{(1)}$. $\mathbb E(\mathcal A(Y)\mathbb 1_B)$ is the set integral $\int_B\mathcal A(Y)\,d\mathbb P$. $A_B$ and the infimum in (2.50) are computed in `EReal` (an infimum over an empty set is $+\infty$, an unbounded one $-\infty$), so neither has a junk value. The conditional expectation is Mathlib's `P[Z|m]`, which equals the true conditional expectation because every theorem assumes $\mathcal F_1\subseteq\mathcal F$ and $Z$ is integrable. In (2.50) the set $S$ lives in `Lp ℝ ⊤ P`.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 66–67, Definition 2.50; p. 68, Eq. (2.46) and Theorem 2.51 (the set S_B); p. 69, Eq. (2.50)

import Mathlib

namespace RiskFunctionals.Conditional

open MeasureTheory

/-- A conditional acceptability mapping with observable information `ℱ₁` (Pflug & Römisch,
*Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 67, Definition 2.50).
The setting (pp. 66–67): `(Ω, ℱ, P)` a probability space (`mΩ` is `ℱ`), `ℱ₁ ⊆ ℱ` a σ-field
(`m`), `𝒴 = L_p(Ω, ℱ, P)` (`Lp ℝ p P`) and `𝒴₁ = L_p(Ω, ℱ₁, P)`, realised as the closed
subspace `lpMeas ℝ ℝ m p P` of classes in `𝒴` that have an `ℱ₁`-measurable version. Elements of
`Lp` are classes of almost surely equal functions, and all (in)equalities between random variables
hold `P`-almost surely, as the book stipulates on p. 67. A mapping `𝒜 : 𝒴 → 𝒴₁` must satisfy:
* (CA1) predictable translation-equivariance: `𝒜(Y + Y⁽¹⁾) = 𝒜(Y) + Y⁽¹⁾` for `Y ∈ 𝒴`,
  `Y⁽¹⁾ ∈ 𝒴₁` (the page prints `𝒜(Y + Y¹)`, a typo for `Y⁽¹⁾`);
* (CA2) concavity: `𝒜(λY + (1 − λ)Y') ≥ λ𝒜(Y) + (1 − λ)𝒜(Y')` for `λ ∈ [0, 1]`;
* (CA3) monotonicity: `Y ≤ Y'` implies `𝒜(Y) ≤ 𝒜(Y')`. -/
structure IsConditionalAcceptabilityMapping {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {P : Measure[mΩ] Ω} {p : ENNReal} (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) : Prop where
  /-- (CA1) Predictable translation-equivariance. -/
  translation : ∀ (Y : Lp ℝ p P) (Y₁ : lpMeas ℝ ℝ m p P),
    ∀ᵐ ω ∂P, (A (Y + (Y₁ : Lp ℝ p P)) : Lp ℝ p P) ω = (A Y : Lp ℝ p P) ω + (Y₁ : Lp ℝ p P) ω
  /-- (CA2) Concavity. -/
  concave : ∀ (Y Y' : Lp ℝ p P) (t : ℝ), 0 ≤ t → t ≤ 1 →
    ∀ᵐ ω ∂P, t * (A Y : Lp ℝ p P) ω + (1 - t) * (A Y' : Lp ℝ p P) ω
      ≤ (A (t • Y + (1 - t) • Y') : Lp ℝ p P) ω
  /-- (CA3) Monotonicity. -/
  monotone : ∀ (Y Y' : Lp ℝ p P), (∀ᵐ ω ∂P, Y ω ≤ Y' ω) →
    ∀ᵐ ω ∂P, (A Y : Lp ℝ p P) ω ≤ (A Y' : Lp ℝ p P) ω

/-- Positive homogeneity of a conditional acceptability mapping (p. 67, Definition 2.50):
`𝒜(λY) = λ𝒜(Y)` for every `λ > 0` (almost surely). -/
def IsPositivelyHomogeneous {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {p : ENNReal} (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) : Prop :=
  ∀ (Y : Lp ℝ p P) (t : ℝ), 0 < t →
    ∀ᵐ ω ∂P, (A (t • Y) : Lp ℝ p P) ω = t * (A Y : Lp ℝ p P) ω

/-- Upper semicontinuity of a conditional acceptability mapping (p. 67, Definition 2.50): for
every `B ∈ ℱ₁` the real functional `Y ↦ 𝔼(𝒜(Y) 𝟙_B) = ∫_B 𝒜(Y) dP` is upper semicontinuous on
`𝒴` (norm topology of `L_p`). This is not upper semicontinuity of the map into `𝒴₁`. -/
def IsUpperSemicontinuousMapping {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {p : ENNReal} [Fact (1 ≤ p)] (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) : Prop :=
  ∀ B : Set Ω, MeasurableSet[m] B →
    UpperSemicontinuous (fun Y : Lp ℝ p P => ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P)

/-- The pairing `𝔼(Y Z) = ∫ Y Z dP` of `Y ∈ L_p` and `Z ∈ L_q`. Every theorem using it pairs
Hölder-conjugate exponents (`1/p + 1/q = 1`) on a probability space, so `Y Z` is integrable and
the Bochner integral is the true expectation, never the junk value `0`. -/
noncomputable def pairing {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {p q : ENNReal} (Y : Lp ℝ p P) (Z : Lp ℝ q P) : ℝ :=
  ∫ ω, Y ω * Z ω ∂P

/-- The dual function (2.46), p. 68: for `Z ∈ L_q(ℱ)` and `B ∈ ℱ₁`,
`A_B(Z) := inf {𝔼(Y Z) − 𝔼(𝒜(Y) 𝟙_B) : Y ∈ 𝒴}`, an infimum in `[−∞, +∞]` (`EReal`) over all
of `𝒴`; it may be `−∞`. -/
noncomputable def dualFunction {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {p q : ENNReal} (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (B : Set Ω) (Z : Lp ℝ q P) : EReal :=
  ⨅ Y : Lp ℝ p P, ((pairing Y Z - ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)

/-- The set `S_B = {Z ∈ L_q(ℱ) : A_B(Z) ≥ 0}` of Theorem 2.51, p. 68. -/
def dualSet {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} {p : ENNReal}
    (q : ENNReal) (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (B : Set Ω) : Set (Lp ℝ q P) :=
  {Z | 0 ≤ dualFunction A B Z}

/-- The constraints of (2.45), p. 67: `Z ≥ 0` and `𝔼(Z | ℱ₁) = 𝟙_B`, both almost surely.
`P[Z|m]` is Mathlib's conditional expectation; it is the true conditional expectation when
`m ≤ mΩ` and `Z` is integrable, which every theorem using this predicate guarantees (`ℱ₁ ⊆ ℱ`
is a hypothesis, and `Z ∈ L_q` on a probability space with `q ≥ 1`). -/
def IsConditionalDensity {Ω : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) {q : ENNReal} (B : Set Ω) (Z : Lp ℝ q P) : Prop :=
  (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧ P[(Z : Ω → ℝ)|m] =ᵐ[P] B.indicator (fun _ => (1 : ℝ))

/-- The defining relation (2.50) of Theorem 2.52, p. 69, for a set `S ⊆ L_∞(ℱ)`: a class
`Y₁* ∈ L₁(ℱ₁)` satisfies, for every `B ∈ ℱ₁`,
`𝔼(Y₁* 𝟙_B) = inf_{Z ∈ S} {𝔼(Y Z) : Z ≥ 0, 𝔼(Z | ℱ₁) = 𝟙_B}`.
The infimum is taken in `[−∞, +∞]` (`EReal`), so it is `+∞` over an empty constraint set and may
be `−∞`; the relation then fails, as it should, since the left side is real. -/
def SatisfiesDualRelation {Ω : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) (S : Set (Lp ℝ ⊤ P)) (Y : Lp ℝ 1 P) (Y₁ : lpMeas ℝ ℝ m 1 P) : Prop :=
  ∀ B : Set Ω, MeasurableSet[m] B →
    ((∫ ω in B, (Y₁ : Lp ℝ 1 P) ω ∂P : ℝ) : EReal)
      = ⨅ Z ∈ S, ⨅ (_ : IsConditionalDensity m P B Z), ((pairing Y Z : ℝ) : EReal)

end RiskFunctionals.Conditional


