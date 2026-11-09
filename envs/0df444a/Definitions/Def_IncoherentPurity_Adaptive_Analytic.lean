-- Prove2me | Definitions.Def_IncoherentPurity_Adaptive_Analytic
-- name    : IncoherentPurity_Adaptive_Analytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:02.125832+00:00
-- url     : https://prove2.me/theorems/f8f95f14-0c88-45e2-aa31-86879e5b3201
-- title:
--   Stopping coin factories, regular density families, and couplings
-- statement:
--   A coin factory has an independent random seed and decides, from a finite prefix of coin flips, whether to continue or output a Boolean. Stopping probabilities use independent Bernoulli input flips. Almost-sure termination is total stopping mass one; expected input cost is a nonnegative series, so infinite cost remains infinite. The policy has no access to the unknown bias.
--
--   A differentiable density family has nonnegative jointly measurable normalized densities and the almost-everywhere absolute continuity in its real parameter required by Definition 2.2. Scores are logarithmic derivatives; Fisher information uses extended nonnegative integration.
--
--   A coupling is witnessed by two measurable random variables on a common probability space and a measurable event on which they agree. This avoids assuming that the diagonal of an arbitrary outcome space is measurable.
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, definitions and constructions, PDF pp.8–9,20,24–25 = printed pp.8–9,20,24–25; Definition 2.2; Theorem A.1 and Appendix A; Lemma 6.6

import Definitions.Def_IncoherentPurity_Adaptive_Gaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace IncoherentPurity.Adaptive

/-- A stopping decision after finitely many input coin flips. All auxiliary randomness
is sampled independently of the unknown coin bias. `inl ()` requests one more input flip. -/
structure CoinFactory where
  Seed : Type
  seedMS : MeasurableSpace Seed
  seedLaw : @Measure Seed seedMS
  seed_probability : @IsProbabilityMeasure Seed seedMS seedLaw
  decision : (n : ℕ) → Seed × (Fin n → Bool) → Unit ⊕ Bool
  measurable_decision : letI := seedMS; ∀ n, Measurable (decision n)
attribute [instance] CoinFactory.seedMS

def coinLaw (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1-p) • Measure.dirac false

def stopsAt (F : CoinFactory) (n : ℕ) (b : Bool) (h : F.Seed × (Fin n → Bool)) : Prop :=
  F.decision n h = Sum.inr b ∧ ∀ j (hj : j < n),
    F.decision j (h.1,fun i => h.2 ⟨i,lt_trans i.isLt hj⟩) = Sum.inl ()
def stopMass (F : CoinFactory) (p : ℝ) (n : ℕ) (b : Bool) : ℝ≥0∞ :=
  (F.seedLaw.prod (Measure.pi (fun _ : Fin n => coinLaw p))) {h | stopsAt F n b h}
def factoryTerminates (F : CoinFactory) (p : ℝ) : Prop :=
  (∑' n : ℕ, (stopMass F p n false + stopMass F p n true)) = 1
def factoryTrue (F : CoinFactory) (p : ℝ) : ℝ≥0∞ := ∑' n : ℕ, stopMass F p n true
def factoryCost (F : CoinFactory) (p : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * (stopMass F p n false + stopMass F p n true)

/-- Differentiable density families with the parameter absolute continuity of Definition 2.2.
The parameter domain is the interval between the two endpoints. -/
structure DensityFamily (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (a b : ℝ) where
  density : ℝ → Ω → ℝ
  nonnegative : ∀ s x, 0 ≤ density s x
  measurable : Measurable (fun z : ℝ × Ω => density z.1 z.2)
  normalized : ∀ s ∈ Set.uIcc a b, ∫⁻ x, ENNReal.ofReal (density s x) ∂μ = 1
  differentiable : ∀ s ∈ Set.uIcc a b, ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t => density t x) s
  absolutelyContinuous : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun t => density t x) a b

def densityLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {a b : ℝ}
    (F : DensityFamily Ω μ a b) (s : ℝ) :=
  μ.withDensity (fun x => ENNReal.ofReal (F.density s x))
def densityScore {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {a b : ℝ}
    (F : DensityFamily Ω μ a b) (s : ℝ) (x : Ω) :=
  deriv (fun t => Real.log (F.density t x)) s
def densityFisher {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {a b : ℝ}
    (F : DensityFamily Ω μ a b) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((densityScore F s x)^2) ∂densityLaw F s

/-- A coupling witnessed on a measurable probability space, avoiding any assumption
that the diagonal of an arbitrary outcome space is measurable. -/
structure Coupling (Ω : Type*) [MeasurableSpace Ω] (μ ν : Measure Ω) (p : ℝ) where
  Space : Type
  spaceMS : MeasurableSpace Space
  law : @Measure Space spaceMS
  probability : @IsProbabilityMeasure Space spaceMS law
  left : Space → Ω
  right : Space → Ω
  left_measurable : letI := spaceMS; Measurable left
  right_measurable : letI := spaceMS; Measurable right
  left_law : letI := spaceMS; law.map left = μ
  right_law : letI := spaceMS; law.map right = ν
  event : Set Space
  measurable_event : letI := spaceMS; MeasurableSet event
  agree : ∀ x ∈ event, left x = right x
  large : ENNReal.ofReal p ≤ law event

end IncoherentPurity.Adaptive


