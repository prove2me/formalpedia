-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_Markov
-- name    : BramsonQueueing_FIFOKelly_Markov
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:04:47.851494+00:00
-- url     : https://prove2.me/theorems/96e70d1a-4e32-4c37-8901-e5d3ac7037c7
-- title:
--   Continuous-time Markov families, Harris recurrence and petite sets
-- statement:
--   A continuous-time strong Markov family on a metric Borel state space is represented by paths from every initial state, a common probability space, transition probabilities, and complete right-continuous filtrations. Paths are adapted, jointly measurable, and almost surely right continuous. The semigroup and stopping-time conditional-law identities are explicit. Harris recurrence means that some nonzero sigma-finite measure assigns positive mass only to measurable sets with almost surely infinite occupation time, from every starting point. Positive Harris recurrence additionally requires an invariant probability measure:
--   $$\pi(B)=\int P^t(x,B)\,\pi(dx).$$
--   A petite set is nonempty and measurable and admits a nonzero common minorant after mixing transition kernels by a probability law on strictly positive times. Uniform smallness on an interval uses the same minorant at every time of that interval. None of these concepts is defined through a drift inequality or through queueing stability. Nonnegative time is represented by nonnegative reals; occupation is Lebesgue integration on the nonnegative real half-line.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 84–90; PDF 92–98

import Mathlib

namespace BramsonQueueing.FIFOKelly

open MeasureTheory Set Filter
open scoped ENNReal NNReal

/-- A continuous-time strong Markov family with a usual filtration. The
conditional-law identity is expressed by integrals over stopping-time events. -/
structure MarkovFamily (S Ω : Type) [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [MeasurableSpace Ω] where
  probability : Measure Ω
  probability_one : IsProbabilityMeasure probability
  path : S → ℝ≥0 → Ω → S
  transition : ℝ≥0 → S → Measure S
  filtration : S → ℝ≥0 → MeasurableSpace Ω
  filtration_le : ∀ x t, filtration x t ≤ ‹MeasurableSpace Ω›
  filtration_mono : ∀ x, Monotone (filtration x)
  filtration_right : ∀ x t, filtration x t = ⨅ (s : ℝ≥0) (_ : t < s), filtration x s
  filtration_complete : ∀ x t (N B : Set Ω), MeasurableSet N → probability N = 0 →
    B ⊆ N → @MeasurableSet Ω (filtration x t) B
  adapted : ∀ x t, @Measurable Ω S (filtration x t) _ (path x t)
  joint_path : ∀ x, Measurable (fun z : ℝ≥0 × Ω => path x z.1 z.2)
  starts : ∀ x, ∀ᵐ ω ∂probability, path x 0 ω = x
  right_paths : ∀ x, ∀ᵐ ω ∂probability, ∀ t,
    ContinuousWithinAt (fun s => path x s ω) (Ici t) t
  kernel_probability : ∀ t x, IsProbabilityMeasure (transition t x)
  kernel_measurable : ∀ B, MeasurableSet B →
    Measurable (fun z : ℝ≥0 × S => transition z.1 z.2 B)
  transition_law : ∀ t x, transition t x = Measure.map (path x t) probability
  semigroup : ∀ s t x B, MeasurableSet B →
    transition (s+t) x B = ∫⁻ y, transition t y B ∂transition s x
  strong_markov : ∀ x (τ : Ω → ℝ≥0),
    (∀ t, @MeasurableSet Ω (filtration x t) {ω | τ ω ≤ t}) →
    ∀ E : Set Ω,
    (∀ t, @MeasurableSet Ω (filtration x t) (E ∩ {ω | τ ω ≤ t})) →
    ∀ t B, MeasurableSet B →
      (∫⁻ ω in E, (B.indicator (fun _ => (1 : ℝ≥0∞))) (path x (τ ω + t) ω)
        ∂probability) =
      ∫⁻ ω in E, transition t (path x (τ ω) ω) B ∂probability

noncomputable def occupation {S Ω : Type} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [MeasurableSpace Ω] (F : MarkovFamily S Ω)
    (x : S) (B : Set S) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ici 0, B.indicator (fun _ => (1 : ℝ≥0∞))
    (F.path x (Real.toNNReal t) ω)

def HarrisRecurrent {S Ω : Type} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [MeasurableSpace Ω] (F : MarkovFamily S Ω) : Prop :=
  ∃ φ : Measure S, φ ≠ 0 ∧ SigmaFinite φ ∧
    ∀ B, MeasurableSet B → 0 < φ B → ∀ x,
      ∀ᵐ ω ∂F.probability, occupation F x B ω = ⊤

def Invariant {S Ω : Type} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [MeasurableSpace Ω] (F : MarkovFamily S Ω) (π : Measure S) : Prop :=
  SigmaFinite π ∧
    ∀ t B, MeasurableSet B → π B = ∫⁻ x, F.transition t x B ∂π

def PositiveHarris {S Ω : Type} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [MeasurableSpace Ω] (F : MarkovFamily S Ω) : Prop :=
  HarrisRecurrent F ∧ ∃ π : Measure S, IsProbabilityMeasure π ∧ Invariant F π

def Petite {S Ω : Type} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [MeasurableSpace Ω] (F : MarkovFamily S Ω) (A : Set S) : Prop :=
  A.Nonempty ∧ MeasurableSet A ∧
    ∃ a : Measure ℝ≥0, IsProbabilityMeasure a ∧ a {0} = 0 ∧
      ∃ ν : Measure S, ν ≠ 0 ∧ ∀ x ∈ A, ∀ B, MeasurableSet B →
        ν B ≤ ∫⁻ t, F.transition t x B ∂a

def UniformlySmall {S Ω : Type} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [MeasurableSpace Ω] (F : MarkovFamily S Ω)
    (A : Set S) (s₁ s₂ : ℝ≥0) : Prop :=
  A.Nonempty ∧ MeasurableSet A ∧ 0 < s₁ ∧ s₁ < s₂ ∧
    ∃ ν : Measure S, ν ≠ 0 ∧ ∀ x ∈ A, ∀ t ∈ Icc s₁ s₂,
      ∀ B, MeasurableSet B → ν B ≤ F.transition t x B

end BramsonQueueing.FIFOKelly


