-- Prove2me | Definitions.Def_MultistageStochastic_RiskFunctional
-- name    : MultistageStochastic_RiskFunctional
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T16:37:45.581104+00:00
-- url     : https://prove2.me/theorems/ed32ce54-2b0e-4607-8047-c64d27fb24ad
-- title:
--   Risk functionals, version independence, Value-at-Risk and Average Value-at-Risk
-- statement:
--   This file fixes the risk functionals of Pflug and Pichler's Chapter 3.
--
--   **Risk functionals.** A random variable $Y$ is read as a **loss**, and a risk functional assigns
--   it a number to be made small. Definition 3.2 lists the axioms:
--
--   1. **(M) Monotonicity:** $\mathcal R(Y_1)\le\mathcal R(Y_2)$ whenever $Y_1\le Y_2$ almost surely;
--   2. **(C) Convexity:** $\mathcal R\bigl((1-t)Y_0+tY_1\bigr)\le(1-t)\mathcal R(Y_0)+t\mathcal R(Y_1)$ for $0\le t\le 1$;
--   3. **(T) Translation equivariance:** $\mathcal R(Y+c)=\mathcal R(Y)+c$ for real $c$;
--   4. **(H) Positive homogeneity:** $\mathcal R(tY)=t\,\mathcal R(Y)$ for $t>0$.
--
--   The source reserves the unqualified term *risk functional* for a functional satisfying all four —
--   "here we shall mention explicitly, if a risk functional is not positively homogeneous" — which is
--   what is elsewhere called a **coherent** risk measure.
--
--   **Version independence.** Definition 3.12: $\mathcal R$ is **version independent**, or law
--   invariant, when $\mathcal R(Y)=\mathcal R(Y')$ whenever $P(Y\le y)=P(Y'\le y)$ for every real $y$.
--
--   **Value-at-Risk and its average.** The **Value-at-Risk** at level $\alpha$ is the lower inverse
--   of the distribution function,
--
--   $$
--   \mathsf{V@R}_\alpha(Y):=\inf\{y:\;P(Y\le y)\ge\alpha\},
--   $$
--
--   and the (upper) **Average Value-at-Risk** averages it over the upper tail,
--
--   $$
--   \mathsf{AV@R}_\alpha(Y):=\frac1{1-\alpha}\int_\alpha^1 \mathsf{V@R}_p(Y)\,\mathrm dp
--   \qquad(0\le\alpha<1),
--   $$
--
--   extended to $\alpha=1$ by the limit, which the source identifies with the essential supremum
--   $\operatorname{ess\,sup}(Y)=\sup\{y:\;G_Y(y)<1\}$.
--
--   **Atomless spaces.** A probability space is **without atoms** when every set of positive measure
--   contains a subset of strictly smaller positive measure.
--
--   **Formalization Note** `L^∞` is spelled out as "measurable and almost surely bounded", and every
--   axiom is quantified over that class rather than over a quotient space, so no `L^p` quotient
--   construction is needed and a risk functional is an ordinary function on random variables. The
--   essential supremum is taken in the source's own form $\sup\{y:G_Y(y)<1\}$, which avoids
--   committing to a particular lattice-theoretic `essSup`. `Atomless` is stated in the splitting
--   form, which is the standard meaning of "probability space without atoms" and is strictly stronger
--   than requiring singletons to be null on a general measurable space.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.1, printed p. 96 (PDF p. 109): Definition 3.1 and Definition 3.2 (axioms (M), (C), (T), (H)); Section 3.2, printed p. 97 (PDF p. 110): Definition 3.3 (Average Value-at-Risk, (3.1)) and the Value-at-Risk (3.2), and the essential supremum as sup{y : G_Y(y) < 1}; Section 3.3, printed p. 103 (PDF p. 116): Definition 3.12 (version independence) and the atomless hypothesis of Theorem 3.13.

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The random variables the risk functionals of Chapter 3 act on: `L^∞`, the measurable and
essentially bounded functions.  Pflug and Pichler, *Multistage Stochastic Optimization*, §3.1,
p. 96. -/
def MemLinfty (P : Measure Ω) (Y : Ω → ℝ) : Prop :=
  Measurable Y ∧ ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C

/-- Definition 3.2, the axioms for a **positively homogeneous risk functional** — what the book
calls a risk functional unless it says otherwise, and what is elsewhere called a coherent risk
measure: monotonicity (M), convexity (C), translation equivariance (T) and positive homogeneity
(H).  Pflug and Pichler, §3.1, p. 96. -/
structure IsRiskFunctional (P : Measure Ω) (R : (Ω → ℝ) → ℝ) : Prop where
  /-- (M) `R Y₁ ≤ R Y₂` whenever `Y₁ ≤ Y₂` almost surely. -/
  mono : ∀ Y₁ Y₂, MemLinfty P Y₁ → MemLinfty P Y₂ → (∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) → R Y₁ ≤ R Y₂
  /-- (C) `R` is convex along linear interpolation. -/
  convex : ∀ Y₀ Y₁ (t : ℝ), MemLinfty P Y₀ → MemLinfty P Y₁ → 0 ≤ t → t ≤ 1 →
    R (fun ω => (1 - t) * Y₀ ω + t * Y₁ ω) ≤ (1 - t) * R Y₀ + t * R Y₁
  /-- (T) adding a constant to the loss adds it to the risk. -/
  translation : ∀ Y (c : ℝ), MemLinfty P Y → R (fun ω => Y ω + c) = R Y + c
  /-- (H) `R` is positively homogeneous. -/
  homogeneous : ∀ Y (t : ℝ), MemLinfty P Y → 0 < t → R (fun ω => t * Y ω) = t * R Y

/-- Definition 3.12: a functional is **version independent** (law invariant) when its value
depends on the distribution of its argument only.  Pflug and Pichler, §3.3, p. 103. -/
def VersionIndependent (P : Measure Ω) (R : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Y Y', MemLinfty P Y → MemLinfty P Y' →
    (∀ y : ℝ, P {ω | Y ω ≤ y} = P {ω | Y' ω ≤ y}) → R Y = R Y'

/-- The **Value-at-Risk** at level `α`, formula (3.2): `inf {y : P(Y ≤ y) ≥ α}`, the lower
inverse of the distribution function.  Pflug and Pichler, §3.2, p. 97. -/
noncomputable def valueAtRisk (P : Measure Ω) (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  sInf {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}}

/-- The essential supremum in the form the source uses, `ess sup Y = sup {y : G_Y(y) < 1}`.
Pflug and Pichler, §3.2, p. 97. -/
noncomputable def essSupBook (P : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  sSup {y : ℝ | P {ω | Y ω ≤ y} < 1}

/-- The (upper) **Average Value-at-Risk** at level `α`, Definition 3.3 (3.1):
`AV@R_α(Y) = (1-α)⁻¹ ∫_α^1 V@R_p(Y) dp` for `α ∈ [0,1)`, extended to `α = 1` by the limit, which
the source identifies with the essential supremum.  Pflug and Pichler, §3.2, p. 97. -/
noncomputable def averageValueAtRisk (P : Measure Ω) (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  if α = 1 then essSupBook P Y
  else (1 - α)⁻¹ * ∫ p in Set.Ioo α 1, valueAtRisk P Y p

/-- A probability space is **without atoms** when every set of positive measure splits into two
sets of smaller, positive measure.  The hypothesis of Kusuoka's theorem, Pflug and Pichler,
§3.3.1, p. 103. -/
def Atomless (P : Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < P s →
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ 0 < P t ∧ P t < P s

/-- The measures appearing in a Kusuoka representation: probability measures carried by the unit
interval.  Pflug and Pichler, §3.3.1, p. 103. -/
def IsKusuokaMeasure (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0

end MultistageStochastic


