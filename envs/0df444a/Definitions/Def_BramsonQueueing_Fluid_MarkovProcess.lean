-- Prove2me | Definitions.Def_BramsonQueueing_Fluid_MarkovProcess
-- name    : BramsonQueueing_Fluid_MarkovProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:13.078525+00:00
-- url     : https://prove2.me/theorems/9becf6a4-bd55-4858-ac86-5cc5a4ba4892
-- title:
--   General-state strong Markov families, Harris recurrence, and petite sets
-- statement:
--   The state space is a locally compact separable metric space with its Borel sigma algebra. A Markov family gives probability laws $\mathbb P_x$, jointly measurable processes $X^x$, right-continuous paths, an adapted complete right-continuous filtration, and a measurable probability transition semigroup. Strong Markov is imposed by the conditional integral identity at every stopping time, restricted to its finite part. No Feller property is required.
--   For a measurable set $A$ and delay $\delta\ge0$, set
--   $$\tau_A(\delta)=\inf\{t\ge\delta:X(t)\in A\},\qquad \eta_A=\int_0^\infty\mathbf1_A(X(t))\,dt.$$
--   An empty hitting-time set has infimum $+\infty$. Harris recurrence means there exists a nonzero sigma-finite measure $\varphi$ such that $\varphi(A)>0$ implies $\mathbb P_x(\eta_A=\infty)=1$ for every $x$. Positive Harris recurrence additionally requires an invariant probability measure. Petite sets are nonempty measurable sets admitting one nonzero measure minorized by a common probability mixture of the transition laws over strictly positive times. Uniform smallness uses a single minorizing measure at every time of the stated interval. Ergodicity is convergence from each state to an invariant probability in total variation, expressed as a uniform bound over measurable events. Nonnegative expectations use extended nonnegative integrals throughout. The helper Invariant tests the semigroup identity for any measure; in the source recurrence and ergodicity notions it is used only with probability measures, which are automatically sigma-finite.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Section 4.1, printed 84–90 / PDF 92–98, equations (4.4)–(4.22).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

/-- A right continuous strong Markov family on a locally compact separable
metric Borel space. The filtration has the usual null-set and right continuity
properties. Strong Markov is stated as the integral identity at stopping times,
on their finite part, so no recurrence or moment conclusion is a field. -/
structure MarkovProcess (S Ω : Type*) [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace Ω] where
  law : S → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (law x)
  X : S → ℝ≥0 → Ω → S
  filtration : S → Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)
  adapted : ∀ x t, Measurable[filtration x t] (X x t)
  jointly_measurable : ∀ x, Measurable (fun p : ℝ≥0 × Ω => X x p.1 p.2)
  initial : ∀ x, ∀ᵐ ω ∂law x, X x 0 ω = x
  right_continuous : ∀ x, ∀ᵐ ω ∂law x, ∀ t,
    ContinuousWithinAt (fun s => X x s ω) (Set.Ici t) t
  complete : ∀ x t (A B : Set Ω), MeasurableSet B → law x B = 0 → A ⊆ B →
    MeasurableSet[filtration x t] A
  filtration_right_continuous : ∀ x t, filtration x t = ⨅ s > t, filtration x s
  transition : ℝ≥0 → S → Measure S
  transition_probability : ∀ t x, IsProbabilityMeasure (transition t x)
  transition_measurable : ∀ B : Set S, MeasurableSet B →
    Measurable (fun p : ℝ≥0 × S => transition p.1 p.2 B)
  transition_law : ∀ x t B, MeasurableSet B →
    transition t x B = law x {ω | X x t ω ∈ B}
  semigroup : ∀ s t x B, MeasurableSet B →
    transition (s + t) x B = ∫⁻ y, transition t y B ∂transition s x
  strong_markov : ∀ x (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (filtration x) τ) (t : ℝ≥0) (A : Set Ω)
    (B : Set S), MeasurableSet[hτ.measurableSpace] A → MeasurableSet B →
    (∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤},
      Set.indicator B (fun _ => (1 : ℝ≥0∞)) (X x ((τ ω).untopD 0 + t) ω) ∂law x) =
    ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, transition t (X x ((τ ω).untopD 0) ω) B ∂law x

variable {S Ω : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]

/-- Hitting time with delay, including infinity when the set is never visited. -/
noncomputable def hittingTime (p : MarkovProcess S Ω) (A : Set S)
    (δ : ℝ≥0) (x : S) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : δ ≤ t) (_ : p.X x t ω ∈ A), (t : ℝ≥0∞)

noncomputable def expectedHitting (p : MarkovProcess S Ω) (A : Set S)
    (δ : ℝ≥0) (x : S) : ℝ≥0∞ := ∫⁻ ω, hittingTime p A δ x ω ∂p.law x

noncomputable def occupation (p : MarkovProcess S Ω) (A : Set S)
    (x : S) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Set.Ici 0,
    Set.indicator A (fun _ => (1 : ℝ≥0∞)) (p.X x t.toNNReal ω)

/-- Harris recurrence is occupation of every positive irreducibility-measure set
for infinite time, not a Foster criterion. -/
def Harris (p : MarkovProcess S Ω) : Prop :=
  ∃ φ : Measure S, φ ≠ 0 ∧ SigmaFinite φ ∧
    ∀ A : Set S, MeasurableSet A → 0 < φ A →
      ∀ x, p.law x {ω | occupation p A x ω = ⊤} = 1

def Invariant (p : MarkovProcess S Ω) (π : Measure S) : Prop :=
  ∀ t A, MeasurableSet A → π A = ∫⁻ x, p.transition t x A ∂π

def PositiveHarris (p : MarkovProcess S Ω) : Prop :=
  Harris p ∧ ∃ π : Measure S, IsProbabilityMeasure π ∧ Invariant p π

/-- Nonempty measurable petite set, with its sampling law supported on positive times. -/
def Petite (p : MarkovProcess S Ω) (A : Set S) : Prop :=
  A.Nonempty ∧ MeasurableSet A ∧
  ∃ a : Measure ℝ≥0, IsProbabilityMeasure a ∧ a {0} = 0 ∧
  ∃ ν : Measure S, ν ≠ 0 ∧ ∀ x ∈ A, ∀ B : Set S, MeasurableSet B →
    ν B ≤ ∫⁻ t, p.transition t x B ∂a

def UniformlySmall (p : MarkovProcess S Ω) (A : Set S) (s₁ s₂ : ℝ≥0) : Prop :=
  A.Nonempty ∧ MeasurableSet A ∧ ∃ ν : Measure S, ν ≠ 0 ∧
    ∀ t ∈ Set.Icc s₁ s₂, ∀ x ∈ A, ∀ B : Set S, MeasurableSet B →
      ν B ≤ p.transition t x B

/-- Total variation convergence, expressed by its uniform measurable-event bound. -/
def Ergodic (p : MarkovProcess S Ω) : Prop :=
  ∃ π : Measure S, IsProbabilityMeasure π ∧ Invariant p π ∧
    ∀ x, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ≥0, ∀ t ≥ T, ∀ B : Set S,
      MeasurableSet B → |(p.transition t x B).toReal - (π B).toReal| < ε

noncomputable def expectedSize (p : MarkovProcess S Ω) (size : S → ℝ≥0)
    (x : S) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, (size (p.X x t ω) : ℝ≥0∞) ∂p.law x

end BramsonQueueing.Fluid


